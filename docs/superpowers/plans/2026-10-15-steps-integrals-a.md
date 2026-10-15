# Steps, part 2a (integrals: rules, u-substitution, parts) Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** `2nd` `F4` on an integral's answer (indefinite or definite) shows textbook steps: the basic rules and table, u-substitution (with the integral in u traced and the substitution back), integration by parts (LIATE, repeated, and the integral appearing again), and the evaluation at the bounds. Every step is checked.

**Architecture:** In `src/steps.cc`, next to the derivative tracer and with its helpers (`sym1`, `sym2`, `mul`, `neg`, `add`, `prod`, `pw`, `txt`, `m`, `args`, `free_of`, `is_op`, `equal`, `plain_minus`), an integral tracer expands unevaluated `integrate(f,v)` nodes one rule at a time (`irule`), leftmost first (`iexpand`, `itrace`). A step is checked by differentiating the whole expression (an `integrate` node differentiates to its integrand; `derive` does not know a parsed `a-b`, so `plain_minus` first): its derivative must equal the integrand (`anti`). A u-substitution traces the integral in u on its own (checked in u) inside the rule, its steps shown before the substitution back. `steps_build` dispatches `diff(` and `integrate(` inputs.

**Tech Stack:** as part 1 (C++14 for CEdev v14.2 / eZ80 with uSTL; giac; WSL builds; CEmu headless; tools/hostgiac host build).

**Spec:** `docs/superpowers/specs/2026-10-14-steps-design.md` (Integral tracer items 1-3, verification, errors). Part 2b (partial fractions, trig integrals, trig substitution) is a separate plan.

## Global Constraints

- The app must fit in 43 flash pages: `_DEMO.bin` at most 2,818,045 B. Room at the start: 32,654 B (en, 718d6a1). Measure after every task; past the cap: stop and ask the user (program editor or Laplace removal needs their agreement).
- UNITS=1 builds without the steps (`NO_STEPS`): new code stays inside `steps.cc`'s `#ifndef NO_STEPS`.
- No regression on the 715-problem emulator suite (DIFF/TIMEOUT/HANG lines identical to `$KB/results/baseline_v1.9.txt.diff`); host steps tests (`tests/host/run_steps_tests.sh`) all pass.
- A wrong step is never shown: any failed check gives "No steps for this one. The answer is still correct."
- Steps are computed only on `2nd` `F4`; giac's engine and `answer.cc` unchanged.
- No attribution lines in commits; push each commit to `origin steps`.
- Commands: build `FLOWCE_WSL_DISTRO=Ubuntu KB=/home/toadvine/flowce-build tools/dev/build.sh en`; host tests via the scratchpad script `steptest.sh` (runs `HG_BUILD=~/flowce-build/hostgiac-steps tests/host/run_steps_tests.sh`); WSL commands through script files.

## Review Focus

- An integral the tracer cannot explain (`integrate(e^(x^2),x)`, `integrate(sin(x)^3,x)` until part 2b): "No steps", not a wrong or partial trace (Task 1, Task 2 cases).
- A problem already using the letter u (`integrate(u*cos(u^2),u)`): the substitution variable must be another letter (Task 2 case).
- A definite integral whose FlowCE answer is a decimal (numeric integration): the evaluation check must accept the decimal, or give "No steps", never a mismatched value (Task 1 case `integrate(sqrt(1+x^3),x,0,1)` expects NONE).
- Parts that do not terminate (`integrate(e^x/x,x)`): bounded (at most 4 parts per problem), then "No steps" (Task 3 case).
- The integral appearing again with another coefficient (`integrate(e^(2x)*cos(x),x)`): the solved value is right (Task 3 case).

---

### Task 1: Integral core (rules, table, + C, definite integrals)

**Files:**
- Modify: `src/steps.cc` (new section before `steps_applicable`; `steps_applicable`; `steps_build`)
- Modify: `tests/host/steps_cases.txt`

**Interfaces:**
- Consumes (part 1, in `steps.cc`): `sym1`, `sym2`, `free_of`, `is_op`, `args`, `mul`, `neg`, `add`, `prod`, `pw`, `plain_minus`, `txt`, `m`, `equal`, `step`, `STEPS_*`.
- Produces (static, in `steps.cc`): `gen inode(f,v)`; `bool anti(E,f,v)`; `gen dvar(v)`; `bool irule(f,v,r,label,choice,pre)`; `int iexpand(E,v,label,choice,pre)`; `int itrace(E,f,v,out)`; `int build_integral(in,answer,problem,out)` (called by `steps_build`). Later tasks add `usub(...)`, `parts(...)`, `again(...)` and call them from `irule` / `itrace`.

- [ ] **Step 1: Failing cases**

Append to `tests/host/steps_cases.txt`, before the `# a stored variable` block:

```text
# integrals (part 2a, task 1)
integrate(3x^2+2x+1,x) :: Sum rule, Constant multiple rule, Power rule, Constant rule
integrate(x^-2,x) :: Power rule
integrate(1/x,x) :: Log rule
integrate(sqrt(x),x) :: Power rule
integrate(5/x^3,x) :: Rewrite as a power, Power rule
integrate(cos(x),x) :: Integral of cos
integrate(e^x,x) :: Integral of exp
integrate(sec(x)^2,x) :: Integral of sec^2
integrate(2^x,x) :: Exponential rule
integrate(1/(1+x^2),x) :: Integral of 1/(1+x^2)
integrate(x^2,x,0,3) :: Power rule, Evaluate at the bounds
integrate(e^(x^2),x) :: NONE
integrate(sqrt(1+x^3),x,0,1) :: NONE
```

and in the stored-variable block, after `diff(x*y,x) :: NONE`:

```text
integrate(y,x) :: NONE
```

Run the scratchpad `steptest.sh`. Expected: the new cases fail (`NO STEPS` / `LABELS`), the rest pass.

- [ ] **Step 2: The integral tracer core**

In `src/steps.cc`, before `int steps_applicable`, add:

```cpp
// ---------------------------------------------------------------- integrals
// As for derivatives: the problem's unevaluated integrate(f,v) nodes are expanded one rule at a
// time, leftmost first. A step is checked by differentiating it (a node differentiates to its
// integrand): the derivative must be the integrand. A u-substitution traces the integral in u on
// its own, checked in u, before the substitution back (usub).
static gen inode(const gen & f,const gen & v){ return sym2(at_integrate,f,v); }
// dx, du: the differential of v, for the choice lines
static gen dvar(const gen & v){ return gen("d"+v.print(contextptr),contextptr); }
// E (its integrate nodes unevaluated) is an antiderivative of f in v (derive does not know a
// parsed a-b: plain_minus first; with no node left the derivative can be evaluated)
static bool anti(const gen & E,const gen & f,const gen & v){
  return equal(eval(derive(plain_minus(E),v,contextptr),1,contextptr),eval(f,1,contextptr));
}

// the textbook table for an argument that is v itself; 0 if f is not in it
static gen table_int(const gen & f,const gen & v,string & label){
  if (f.type!=_SYMB) return 0;
  const unary_function_ptr & s=f._SYMBptr->sommet;
  const vecteur a=args(f);
  gen r;
  if (a.size()==1 && a[0]==v){
    if (s==at_exp) r=f;
    else if (s==at_sin) r=neg(sym1(at_cos,v));
    else if (s==at_cos) r=sym1(at_sin,v);
    else if (s==at_tan) r=neg(sym1(at_ln,sym1(at_abs,sym1(at_cos,v))));
    else if (s==at_cot) r=sym1(at_ln,sym1(at_abs,sym1(at_sin,v)));
    else if (s==at_sec) r=sym1(at_ln,sym1(at_abs,sym2(at_plus,sym1(at_sec,v),sym1(at_tan,v))));
    else if (s==at_csc) r=neg(sym1(at_ln,sym1(at_abs,sym2(at_plus,sym1(at_csc,v),sym1(at_cot,v)))));
    if (!is_zero(r)){ label=string("Integral of ")+s.ptr()->s; return r; }
  }
  if (s==at_pow && a.size()==2){
    if (a[1]==v && free_of(a[0],v)){ // a^v/ln(a)
      label="Exponential rule";
      return sym2(at_division,f,sym1(at_ln,a[0]));
    }
    if (a[1]==2 && (is_op(a[0],at_sec) || is_op(a[0],at_csc)) && args(a[0])[0]==v){
      const bool sec=is_op(a[0],at_sec);
      label=sec?"Integral of sec^2":"Integral of csc^2";
      return sec?sym1(at_tan,v):neg(sym1(at_cot,v));
    }
  }
  if (s==at_prod && a.size()==2){ // sec(v)*tan(v), csc(v)*cot(v)
    for (int k=0;k<2;++k){
      const gen & p=a[k], & q=a[1-k];
      if (is_op(p,at_sec) && is_op(q,at_tan) && args(p)[0]==v && args(q)[0]==v){ label="Integral of sec*tan"; return sym1(at_sec,v); }
      if (is_op(p,at_csc) && is_op(q,at_cot) && args(p)[0]==v && args(q)[0]==v){ label="Integral of csc*cot"; return neg(sym1(at_csc,v)); }
    }
  }
  if ((s==at_division || s==at_pow) && !contains(f,at_sin) && !contains(f,at_cos) && !contains(f,at_exp) && !contains(f,at_ln)){
    const gen v2=sym2(at_pow,v,2);
    if (equal(f,sym2(at_division,1,sym2(at_plus,1,v2)))){ label="Integral of 1/(1+x^2)"; return sym1(at_atan,v); }
    if (equal(f,sym2(at_division,1,sym1(at_sqrt,sym2(at_binary_minus,1,v2))))){ label="Integral of 1/sqrt(1-x^2)"; return sym1(at_asin,v); }
  }
  return 0;
}

// one rule applied to the integral of f in v: its result r (with integrate nodes left for the
// rest), the rule's name, what was chosen, and steps to show before this one (pre: a
// u-substitution's integral in u); false: no rule
static bool irule(const gen & f,const gen & v,gen & r,string & label,string & choice,vector<step> & pre){
  choice.clear();
  if (free_of(f,v)){ r=mul(f,v); label="Constant rule"; return true; }
  if (f==v){ r=sym2(at_division,sym2(at_pow,v,2),2); label="Power rule"; return true; }
  if (f.type!=_SYMB) return false;
  const unary_function_ptr & s=f._SYMBptr->sommet;
  const vecteur a=args(f);
  if (s==at_plus || s==at_binary_minus){
    vecteur t;
    for (unsigned i=0;i<a.size();++i)
      t.push_back(s==at_binary_minus && i?neg(inode(a[i],v)):inode(a[i],v));
    r=add(t);
    label=s==at_binary_minus?"Difference rule":"Sum rule";
    return true;
  }
  if (s==at_neg){ r=neg(inode(a[0],v)); label="Constant multiple rule"; return true; }
  if (s==at_prod){
    vecteur c,g;
    for (unsigned i=0;i<a.size();++i)
      (free_of(a[i],v)?c:g).push_back(a[i]);
    if (!c.empty() && !g.empty()){ r=mul(prod(c),inode(prod(g),v)); label="Constant multiple rule"; return true; }
  }
  if (s==at_division){
    const gen & p=a[0], & q=a[1];
    if (free_of(q,v)){ r=sym2(at_division,inode(p,v),q); label="Constant multiple rule"; return true; }
    if (is_op(q,at_prod)){ // 1/(2u): the constant factors out
      vecteur c,g;
      const vecteur qa=args(q);
      for (unsigned i=0;i<qa.size();++i)
        (free_of(qa[i],v)?c:g).push_back(qa[i]);
      if (!c.empty() && !g.empty()){
        r=sym2(at_division,inode(sym2(at_division,p,prod(g)),v),prod(c));
        label="Constant multiple rule";
        return true;
      }
    }
    if (free_of(p,v)){ // c/v, c/v^n, c/sqrt(v)
      gen n;
      if (q==v) n=1;
      else if (is_op(q,at_pow) && args(q)[0]==v && free_of(args(q)[1],v)) n=args(q)[1];
      else if (is_op(q,at_sqrt) && args(q)[0]==v) n=fraction(1,2);
      if (is_one(n)){ r=mul(p,sym1(at_ln,sym1(at_abs,v))); label="Log rule"; return true; }
      if (!is_zero(n)){
        const gen e=eval(-n,1,contextptr);
        r=mul(p,inode(sym2(at_pow,v,e),v));
        label="Rewrite as a power";
        choice=m(txt(sym2(at_division,1,q))+" = "+txt(sym2(at_pow,v,e)));
        return true;
      }
    }
  }
  if (s==at_pow && a[0]==v && free_of(a[1],v)){
    const gen e1=eval(a[1]+1,1,contextptr);
    if (is_zero(e1)){ r=sym1(at_ln,sym1(at_abs,v)); label="Log rule"; return true; }
    r=sym2(at_division,pw(v,e1),e1);
    label="Power rule";
    return true;
  }
  if (s==at_sqrt && a[0]==v){
    r=sym2(at_division,sym2(at_pow,v,fraction(3,2)),fraction(3,2));
    label="Power rule";
    choice=m(txt(f)+" = "+txt(sym2(at_pow,v,fraction(1,2))));
    return true;
  }
  r=table_int(f,v,label);
  return !is_zero(r);
}

// the first integrate(.,v) node of E (leftmost, outermost) replaced by its rule: 1 done, 0 no node
// in v left, -1 a node no rule explains
static int iexpand(gen & E,const gen & v,string & label,string & choice,vector<step> & pre){
  if (E.type!=_SYMB) return 0;
  if (E._SYMBptr->sommet==at_integrate){
    const vecteur a=args(E);
    if (a.size()!=2 || !(a[1]==v)) return 0;
    gen r;
    if (!irule(a[0],v,r,label,choice,pre)) return -1;
    E=r;
    return 1;
  }
  vecteur w=args(E);
  for (unsigned i=0;i<w.size();++i){
    const int k=iexpand(w[i],v,label,choice,pre);
    if (!k) continue;
    if (k>0){
      const gen & f=E._SYMBptr->feuille;
      E=symbolic(E._SYMBptr->sommet,f.type==_VECT?gen(w,f.subtype):w[0]);
    }
    return k;
  }
  return 0;
}

// the steps of E (integrate nodes in v), an integral of f, into out until no node is left
static int itrace(gen & E,const gen & f,const gen & v,vector<step> & out){
  for (;;){
    string label,choice;
    vector<step> pre;
    const int r=iexpand(E,v,label,choice,pre);
    if (interrupted) return STEPS_STOPPED;
    if (!r) return STEPS_OK;
    if (r<0 || out.size()+pre.size()>=STEPS_MAX || !anti(E,f,v))
      return interrupted?STEPS_STOPPED:STEPS_NONE;
    for (unsigned i=0;i<pre.size();++i) out.push_back(pre[i]);
    step s={label,choice,txt(E)};
    out.push_back(s);
  }
}

// integrate(f,x) or integrate(f,x,a,b) (in, parsed): its steps, the last being FlowCE's answer
// (+ C for an antiderivative)
static int build_integral(const gen & in,const string & answer,string & problem,vector<step> & out){
  const vecteur a=args(in);
  if ((a.size()!=2 && a.size()!=4) || a[1].type!=_IDNT) return STEPS_NONE;
  const gen & f=a[0], & x=a[1];
  problem=txt(in);
  gen E=inode(f,x);
  const int r=itrace(E,f,x,out);
  if (r!=STEPS_OK){ out.clear(); return r; }
  const gen F=eval(E,1,contextptr),A=eval(gen(answer,contextptr),1,contextptr);
  if (interrupted){ out.clear(); return STEPS_STOPPED; }
  if (a.size()==2){ // FlowCE's antiderivative too (they differ by a constant)
    if (!anti(A,f,x)){ out.clear(); return interrupted?STEPS_STOPPED:STEPS_NONE; }
    step s={out.empty() || out.back().expr!=answer?"Simplify":"Add the constant","",answer+"+C"};
    out.push_back(s);
    return STEPS_OK;
  }
  // F(b)-F(a), substituted as written, then the value
  const gen V=sym2(at_plus,quotesubst(F,x,a[3],contextptr),neg(quotesubst(F,x,a[2],contextptr)));
  const gen d=eval(V,1,contextptr)-A,de=evalf(d,1,contextptr);
  if (interrupted || !(is_zero(ratnormal(d,contextptr)) || (de.type==_DOUBLE_ && std::abs(de._DOUBLE_val)<1e-6*(1+std::abs(evalf(A,1,contextptr)._DOUBLE_val))))){
    out.clear();
    return interrupted?STEPS_STOPPED:STEPS_NONE;
  }
  step s={"Evaluate at the bounds","from "+m(a[2])+" to "+m(a[3]),txt(V)};
  out.push_back(s);
  step t={"Simplify","",answer};
  out.push_back(t);
  return STEPS_OK;
}
```

Notes for the implementer:
- `fraction(1,2)`, `quotesubst`, `evalf`, `ratnormal` are used the same way in answer.cc; `std::abs` on doubles needs `<math.h>` only if the build complains (answer.cc uses `std::abs` already).
- `evalf(A)._DOUBLE_val` is only read when `de` is a double; if `A` is not numeric the first condition decides.

- [ ] **Step 3: Dispatch integrals**

In `steps_applicable` replace the return with:

```cpp
  return !strncmp(s,"diff(",5) || !strncmp(s,"integrate(",10);
```

and update `steps.h`'s comment to "(diff(...), integrate(...))". In `steps_build`, after the stored-variable check needs the variable, so restructure the start: after `const gen in(buf,contextptr); free(buf);` replace `if (!is_op(in,at_diff)) return STEPS_NONE;` with:

```cpp
  if (is_op(in,at_integrate)){
    const vecteur a=args(in);
    if (a.size()<2 || a[1].type!=_IDNT) return STEPS_NONE;
    const vecteur ids=lidnt(a[0]);
    for (unsigned i=0;i<ids.size();++i)
      if (ids[i]!=a[1] && contains(eval(ids[i],1,contextptr),a[1])) return STEPS_NONE;
    return build_integral(in,answer,problem,out);
  }
  if (!is_op(in,at_diff)) return STEPS_NONE;
```

- [ ] **Step 4: Run the host tests**

Expected: all cases pass. Read each new trace (`/tmp/steps_out.txt` in WSL): `integrate(3x^2+2x+1,x)` ends `x^3+x^2+x+C`; `integrate(x^2,x,0,3)` shows `3^3/3-0^3/3` (or the same with parentheses) then `9`. If `anti` fails on a correct step because `derive` leaves `integrate` nodes underived, write `anti` with the nodes replaced first: collect `lop(E,at_integrate)`, replace each by a fresh symbol `F_k`, derive, then replace `derive(F_k)` by its integrand — and record a Ruling.

- [ ] **Step 5: Build, size, commit**

Build `en`; record the size. Commit:

```bash
git add src/steps.cc src/steps.h tests/host/steps_cases.txt
git commit -m "Steps: integrals, the basic rules and table (+ C, definite integrals at the bounds)"
git push -q origin steps
```

---

### Task 2: u-substitution

**Files:**
- Modify: `src/steps.cc` (before `irule`: `candidates`, `free_var`, `usub`; `irule` calls `usub`; `itrace` is used recursively)
- Modify: `tests/host/steps_cases.txt`

**Interfaces:**
- Consumes: `inode`, `dvar`, `itrace`, `irule` (Task 1).
- Produces: `static void candidates(f,v,c)`, `static gen free_var(f)`, `static bool usub(f,v,r,label,choice,pre)`; a file-level `static int usub_depth`.

- [ ] **Step 1: Failing cases**

Add after the task 1 integral cases:

```text
integrate(cos(3x),x) :: u-substitution, Constant multiple rule, Integral of cos, Substitute back
integrate(2x*cos(x^2),x) :: u-substitution, Integral of cos, Substitute back :: Let `u = x^2`
integrate(x/(x^2+1),x) :: u-substitution, Constant multiple rule, Log rule, Substitute back
integrate((2x+3)/(x^2+3x+1),x) :: u-substitution, Log rule, Substitute back
integrate(x*e^(x^2),x) :: u-substitution, Integral of exp, Substitute back
integrate((x^2+1)^5*x,x) :: u-substitution, Power rule, Substitute back
integrate(sin(x)*cos(x)^2,x) :: u-substitution, Power rule, Substitute back
integrate(u*cos(u^2),u) :: u-substitution, Integral of cos, Substitute back :: Let `w = u^2`
```

Run: these fail (`NO STEPS`).

- [ ] **Step 2: Implement**

Before `irule` add (and declare `itrace` above it: `static int itrace(gen & E,const gen & f,const gen & v,vector<step> & out);`):

```cpp
// the u candidates of f: its functions' arguments, its powers' bases (and exponents over a
// constant base), its denominators, outermost first
static void candidates(const gen & f,const gen & v,vecteur & c){
  if (f.type!=_SYMB) return;
  const unary_function_ptr & s=f._SYMBptr->sommet;
  const vecteur a=args(f);
  gen b;
  if (s==at_pow && a.size()==2) b=free_of(a[1],v)?a[0]:free_of(a[0],v)?a[1]:gen(0);
  else if (s==at_division) b=a[1];
  else if (a.size()==1 && s!=at_neg) b=a[0];
  if (!is_zero(b) && !(b==v) && !free_of(b,v) && !equalposcomp(c,b)) c.push_back(b);
  for (unsigned i=0;i<a.size();++i) candidates(a[i],v,c);
}
// the name of the new variable: u, else w, t, s (not in f, no stored value)
static gen free_var(const gen & f){
  static const char * const n[]={"u","w","t","s"};
  for (int i=0;i<4;++i){
    const gen u(n[i],contextptr);
    if (u.type==_IDNT && !contains(f,u) && eval(u,1,contextptr)==u) return u;
  }
  return 0;
}
static int usub_depth; // u-substitutions inside one another (at most 2)
// u-substitution: f = G(b)*b' for a candidate b; the integral of G(u) in u traced on its own
// (its steps in pre, after the substitution step), then u = b put back
static bool usub(const gen & f,const gen & v,gen & r,string & label,string & choice,vector<step> & pre){
  if (usub_depth>=2) return false;
  vecteur c;
  candidates(f,v,c);
  const gen u=free_var(f);
  if (is_zero(u)) return false;
  for (unsigned i=0;i<c.size();++i){
    const gen & b=c[i];
    const gen db=normal(derive(eval(b,1,contextptr),v,contextptr),contextptr);
    if (is_zero(db) || interrupted) continue;
    // b replaced by u before simplifying: what is left of v must cancel (x/(x^2+1) over 2x: 1/(2u))
    const gen G=normal(quotesubst(sym2(at_division,f,db),b,u,contextptr),contextptr);
    if (!free_of(G,v) || interrupted) continue;
    const size_t n0=pre.size();
    step s={"u-substitution","Let "+m(txt(u)+" = "+txt(b))+", "+m(txt(dvar(u))+" = "+txt(mul(db,dvar(v)))),txt(inode(G,u))};
    pre.push_back(s);
    gen Eu=inode(G,u);
    ++usub_depth;
    const int k=itrace(Eu,G,u,pre);
    --usub_depth;
    if (k!=STEPS_OK){
      pre.resize(n0);
      if (interrupted) return false;
      continue;
    }
    r=quotesubst(Eu,u,b,contextptr);
    label="Substitute back";
    choice=m(txt(u)+" = "+txt(b));
    return true;
  }
  return false;
}
```

In `irule`, replace the final two lines with:

```cpp
  r=table_int(f,v,label);
  if (!is_zero(r)) return true;
  return usub(f,v,r,label,choice,pre);
```

In `steps_build` (start, with `out.clear()`), reset `usub_depth=0;`.

- [ ] **Step 3: Run the host tests**

Expected: all pass. Read the traces: `integrate(2x*cos(x^2),x)` must show `Let u = x^2, du = 2*x*dx`, `∫cos(u) du`, `sin(u)`, `Substitute back` `sin(x^2)`, then `sin(x^2)+C`. If `quotesubst` misses `b` because the parse wrote it differently from `candidates` (e.g. `x^2+3*x+1` vs `3*x+x^2+1`), try `subst` on the evaluated quotient before giving up on that candidate, and record a Ruling.

- [ ] **Step 4: Build, size, commit**

```bash
git add src/steps.cc tests/host/steps_cases.txt
git commit -m "Steps: u-substitution (the integral in u traced, then u put back)"
git push -q origin steps
```

---

### Task 3: Integration by parts

**Files:**
- Modify: `src/steps.cc` (`liate`, `poly_v`, `parts`, `again`; `irule` and `itrace` call them; `steps_build` resets `parts_count`)
- Modify: `tests/host/steps_cases.txt`

**Interfaces:**
- Consumes: `inode`, `dvar`, `irule`, `itrace`, `usub` (Tasks 1-2).
- Produces: `static int parts_count`; `static bool parts(f,v,r,label,choice)`; `static bool again(E,f,v,label,choice)`.

- [ ] **Step 1: Failing cases**

```text
integrate(x*e^x,x) :: Integration by parts, Integral of exp :: u = x
integrate(x^2*e^x,x) :: Integration by parts, Integration by parts, Integral of exp
integrate(x*ln(x),x) :: Integration by parts, Power rule :: u = ln(x)
integrate(ln(x),x) :: Integration by parts, Constant rule
integrate(atan(x),x) :: Integration by parts, u-substitution, Substitute back
integrate(x*sin(x),x,0,pi) :: Integration by parts, Integral of cos, Evaluate at the bounds
integrate(e^x*sin(x),x) :: Integration by parts, Integration by parts, The integral appears again
integrate(e^(2x)*cos(x),x) :: Integration by parts, Integration by parts, The integral appears again
integrate(e^x/x,x) :: NONE
```

Run: they fail.

- [ ] **Step 2: Implement**

Before `irule` add:

```cpp
static bool poly_v(const gen & g,const gen & v){ // a polynomial in v (x, x^2+1, 3x^3)
  const gen e=eval(g,1,contextptr);
  const vecteur l=lvar(e);
  return l.size()==1 && l.front()==v && free_of(_denom(e,contextptr),v);
}
// LIATE: the factor to differentiate (u) is the first of: ln, inverse trig, a polynomial, trig, exponential
static int liate(const gen & g,const gen & v){
  if (contains(g,at_ln) || contains(g,at_log10)) return 0;
  if (contains(g,at_asin) || contains(g,at_acos) || contains(g,at_atan)) return 1;
  if (poly_v(g,v)) return 2;
  if (contains(g,at_sin) || contains(g,at_cos) || contains(g,at_tan) || contains(g,at_sec) || contains(g,at_csc) || contains(g,at_cot)) return 3;
  return 4;
}
static int parts_count; // integrations by parts in this problem (at most 4)
// integration by parts: f = u*dv (u by LIATE, dv the rest, v its antiderivative by giac),
// u*v - integral of v*du
static bool parts(const gen & f,const gen & v,gen & r,string & label,string & choice){
  if (parts_count>=4) return false;
  const vecteur fs=is_op(f,at_prod)?args(f):vecteur(1,f);
  if (fs.size()==1 && liate(f,v)>1) return false; // alone: ln, inverse trig (dv = dx)
  unsigned k=0;
  for (unsigned i=1;i<fs.size();++i)
    if (liate(fs[i],v)<liate(fs[k],v)) k=i;
  vecteur rest;
  for (unsigned i=0;i<fs.size();++i)
    if (i!=k) rest.push_back(fs[i]);
  const gen U=fs[k],dV=rest.empty()?gen(1):prod(rest);
  const gen V=normal(_integrate(makesequence(eval(dV,1,contextptr),v),contextptr),contextptr);
  if (interrupted || is_undef(V) || V.type==_STRNG || contains(V,at_integrate)) return false;
  const gen dU=normal(derive(eval(U,1,contextptr),v,contextptr),contextptr),d=dvar(v);
  ++parts_count;
  r=sym2(at_plus,mul(U,V),neg(inode(normal(mul(V,dU),contextptr),v)));
  label="Integration by parts";
  choice=m("u = "+txt(U))+", "+m("dv = "+txt(mul(dV,d)))+"\n"+m("du = "+txt(mul(dU,d)))+", "+m("v = "+txt(V));
  return true;
}
// the integral of f appearing again in E (by parts twice: e^x sin x): E = A + k*I, so I = A/(1-k)
static bool again(gen & E,const gen & f,const gen & v,string & label,string & choice){
  const vecteur nodes=lop(E,at_integrate);
  if (nodes.size()!=1) return false;
  const gen c=ratnormal(eval(args(nodes[0])[0],1,contextptr)/eval(f,1,contextptr),contextptr);
  if (!free_of(c,v) || is_one(c) || is_zero(c)) return false;
  const gen T("steps_I",contextptr);
  const gen P=eval(plain_minus(quotesubst(E,nodes[0],c*T,contextptr)),1,contextptr);
  const gen k=normal(derive(P,T,contextptr),contextptr);
  if (!free_of(k,T) || !free_of(k,v) || is_one(k)) return false;
  const gen A=normal(subst(P,T,0,false,contextptr),contextptr);
  E=normal(A/(1-k),contextptr);
  label="The integral appears again";
  choice=m("I = "+txt(A)+" + "+txt(k)+"*I")+", so "+m("I = "+txt(A)+"/(1-"+txt(k)+")");
  return true;
}
```

In `irule`, the final line becomes:

```cpp
  return usub(f,v,r,label,choice,pre) || parts(f,v,r,label,choice);
```

In `itrace`, after `out.push_back(s);` add:

```cpp
    string l2,c2;
    if (again(E,f,v,l2,c2)){
      if (!anti(E,f,v)) return interrupted?STEPS_STOPPED:STEPS_NONE;
      step t={l2,c2,txt(E)};
      out.push_back(t);
    }
```

In `steps_build`, reset `parts_count=0;` with `usub_depth`.

- [ ] **Step 3: The choice line on two lines (screen)**

In `src/focus_steps.cc`, `choice_line` draws one line; make `item` draw each `\n`-separated line:

```cpp
  if (*choice) { // one line per \n
    char line[160];
    for (const char * p = choice;;) {
      const char * q = strchr(p, '\n');
      int n = q ? q - p : strlen(p);
      if (n > (int)sizeof(line) - 1) n = sizeof(line) - 1;
      memcpy(line, p, n); line[n] = 0;
      h += choice_line(line, y + h, draw);
      if (!q) break;
      p = q + 1;
    }
  }
```

(replacing `if (*choice) h += choice_line(choice, y + h, draw);`). In `tools/hostgiac/khicas_post.cc`, the choice's `\n` prints as ` / ` (after the backquote replacement: `if (c[j]=='\n') c[j]='/';` is enough).

- [ ] **Step 4: Run the host tests**

Expected: all pass. Check by reading: `integrate(x*e^x,x)` choice `u = x, dv = exp(x)*dx / du = dx, v = exp(x)`; `integrate(e^x*sin(x),x)` ends with `I = ...`, value `exp(x)*(sin(x)-cos(x))/2`; `integrate(e^(2x)*cos(x),x)` value `exp(2x)(2cos x + sin x)/5`.

- [ ] **Step 5: Build, size, commit**

```bash
git add src/steps.cc src/focus_steps.cc tests/host/steps_cases.txt tools/hostgiac/khicas_post.cc
git commit -m "Steps: integration by parts (LIATE, repeated, the integral appearing again)"
git push -q origin steps
```

---

### Task 4: On the calculator: screenshots, suite, bundle

**Files:** none in src unless a check fails.

- [ ] **Step 1: Emulator screenshots**

Build `en`, install (`tools/emu/install.py en base`), and capture, typing integrals with the calculus menu (`window` = F2, then `1` Antiderivative or `2` Definite integral) so fractions stay inside the template: `x*e^x`, `2x*cos(x^2)`, `e^x*sin(x)` (antiderivatives), `x*sin(x)` from 0 to π (definite: fill the bounds with the arrow keys as the template orders them; check the typed screenshot before enter). For each: answer, 2nd bar ("steps"), Steps screen, every scroll position to the end. Check: the ∫ … dx layout, the two-line parts choice, `+ C` at the end, "Evaluate at the bounds".

- [ ] **Step 2: Full suite and host tests**

Emulator suite (715): `SAME` against the baseline. Host steps tests: all pass.

- [ ] **Step 3: Bundle and page**

Rebuild `FlowCE.b84` (scratchpad `bundle.sh`), `site/build.sh ../flowce-build-out/FlowCE.b84 v1.9-steps.2`; the local server serves it.

- [ ] **Step 4: Record**

Ledger: sizes per task, suite result, screenshots checked.
