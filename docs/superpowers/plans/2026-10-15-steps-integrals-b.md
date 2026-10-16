# Steps, part 2b (integrals: partial fractions, trig integrals, trig substitution) Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Integral steps for the rest of the spec's Calc 2 techniques: partial fractions (polynomial division, decomposition, splitting the numerator, completing the square), trig integrals (odd powers by the Pythagorean identity, even powers by power reduction, powers of tan, sec³), and trig substitution (x = a sin t, a tan t, a sec t, with the back-substitution by the triangle). Every step checked, as before.

**Architecture:** New rules in `irule` (`src/steps.cc`), each producing integrate nodes for the existing machinery: `table_int` learns linear inner arguments (∫cos(3x) = sin(3x)/3) and ∫1/(w²+k); new rules `expand_rule`, `pfrac` (with `split_num`, `complete_square`), `trig_rewrite`, `trig_sub`. The trig substitution traces the integral in t on its own like `usub` (steps in `pre`, checked in t), then back-substitutes; the outer step is checked in x as all steps are.

**Tech Stack:** as parts 1 and 2a.

**Spec:** `docs/superpowers/specs/2026-10-14-steps-design.md` (Integral tracer items 4-5). Part 2a's machinery: `docs/superpowers/plans/2026-10-15-steps-integrals-a.md`.

## Global Constraints

- `_DEMO.bin` at most 2,818,045 B. Room at the start: 39,031 B (d0a2d61, program editor removed). Measure after every task; stop and report if it crosses 2,812,000 B (keep 6 KB for fixes).
- New code inside `steps.cc`'s `#ifndef NO_STEPS`; giac and answer.cc unchanged.
- No regression: host steps tests all pass (existing cases may change only where this plan says so); the emulator suite (715) SAME as the v1.9 baseline.
- A wrong step is never shown (every step goes through `anti`; rules may only produce integrate nodes and expressions equal to their input).
- Helpers to reuse: `sym1`, `sym2`, `mul`, `neg`, `add`, `prod`, `pw`, `den`, `txt`, `m`, `args`, `free_of`, `is_op`, `equal`, `plain_minus`, `inode`, `dvar`, `anti`, `itrace`, `free_var`, `poly_v`. Size: keep new rules `static __attribute__((noinline))` and build constant expressions from text (`gen("...",contextptr)` + `quotesubst`) where a tree would take many calls.
- No attribution lines in commits; push to `origin steps`.

## Review Focus

- A rational function whose denominator has a repeated linear factor and an irreducible quadratic together (`(x^2+1)/(x*(x^2+1)^2)` simplifies first; `1/(x^3+x)`): every term traced, or "No steps".
- A quadratic with no real roots and a leading coefficient (`1/(4x^2-4x+3)`): completing the square keeps the coefficient right.
- A trig integral with a non-linear argument (`sin(x^2)^3`): no trig rewrite (u would not be linear), "No steps" or another technique.
- A square root that is not one of the three forms (`sqrt(x^2+2x)`, `sqrt(4-9x^2)`): no trig substitution unless the form matches exactly; never a wrong triangle.
- A trig substitution whose integral in t needs a half-angle identity (`sqrt(9-x^2)`): the back-substitution of sin 2t by 2 sin t cos t gives the textbook answer.

---

### Task 1: Linear inner arguments, ∫1/(w²+k), Expand

**Files:** Modify `src/steps.cc` (`table_int`, `irule`), `tests/host/steps_cases.txt`.

**Interfaces:**
- Produces: `static gen lin_coef(const gen & w,const gen & v)` (a of w = a*v+b, 0 if w is not linear or is v); the table matches f(w) for a linear w (result divided by a); `irule` rules "Log rule"/"Power rule" for c/(ax+b)^n and (ax+b)^n, "Integral of 1/(u^2+a^2)" for c/(w^2+k), "Expand" for products and integer powers of sums that are polynomials.

- [ ] **Step 1: Failing cases** — replace the case `integrate(cos(3x),x) :: u-substitution, Constant multiple rule, Integral of cos, Substitute back` with the first line below (the spec's table form), and add the others after the u-substitution cases:

```text
integrate(cos(3x),x) :: Integral of cos :: `u = 3*x`
integrate(e^(2x+1),x) :: Integral of exp
integrate(1/(2x+5),x) :: Log rule
integrate((3x-1)^4,x) :: Power rule
integrate(1/(x+1)^2,x) :: Power rule
integrate(1/(x^2+4),x) :: Integral of 1/(u^2+a^2)
integrate(3/((x+2)^2+9),x) :: Integral of 1/(u^2+a^2)
integrate((x+1)*(x-2),x) :: Expand, Difference rule
integrate((1-x^2)^2,x) :: Expand
```

Run: they fail.

- [ ] **Step 2: Implement**

Before `table_int`:

```cpp
// a of w = a*v+b (w linear in v, not v itself); 0 otherwise
static gen lin_coef(const gen & w,const gen & v){
  gen a,b;
  if (w==v || free_of(w,v) || !is_linear_wrt(w,v,a,b,contextptr) || !free_of(a,v)) return 0;
  return eval(a,1,contextptr);
}
// the argument of f's first table function (exp, sin, cos, tan, cot, sec, csc), 0 if none
static gen inner(const gen & f){
  if (f.type!=_SYMB) return 0;
  const unary_function_ptr & s=f._SYMBptr->sommet;
  if (s==at_exp || s==at_sin || s==at_cos || s==at_tan || s==at_cot || s==at_sec || s==at_csc) return f._SYMBptr->feuille;
  const vecteur a=args(f);
  for (unsigned i=0;i<a.size();++i){ const gen w=inner(a[i]); if (!is_zero(w)) return w; }
  return 0;
}
```

In `table_int`, replace the loop with one that tries `w = v` and, when `inner(f)` is linear, `w = inner(f)` (the result over a):

```cpp
  const gen x("x",contextptr),w0=inner(f),a=is_zero(w0)?gen(0):lin_coef(w0,v);
  for (int pass=0;pass<2;++pass){
    const gen w=pass?w0:v;
    if (pass && is_zero(a)) break;
    for (int k=0;TABLE[k];k+=3){
      if (pass && TABLE[k][0]=='1') continue; // (1/(1+x^2): the argument v only)
      const gen p=quotesubst(gen(TABLE[k+1],contextptr),x,w,contextptr);
      if (f==p || (TABLE[k][0]=='1' && is_op(f,at_division) && equal(f,p))){
        label=string("Integral of ")+TABLE[k];
        const gen r=quotesubst(gen(TABLE[k+2],contextptr),x,w,contextptr);
        if (!pass) return r;
        choice=m("u = "+txt(w))+": divide by "+m(txt(a)); // (table_int gets choice: see below)
        return is_one(a)?r:sym2(at_division,r,den(a));
      }
    }
  }
  return 0;
```

`table_int` needs the choice: change its signature to `table_int(const gen & f,const gen & v,string & label,string & choice)` and its call in `irule` to `table_int(f,v,label,choice)`.

In `irule`, in the `at_division` branch where `free_of(p,v)` (before the `c/v^n` block), add the linear forms and the arctangent form:

```cpp
    if (free_of(p,v)){
      // c/(ax+b), c/(ax+b)^n: ln|ax+b|/a, (ax+b)^(1-n)/((1-n)a)
      gen base=q,n=1;
      if (is_op(q,at_pow) && free_of(args(q)[1],v)){ base=args(q)[0]; n=args(q)[1]; }
      const gen a=lin_coef(base,v);
      if (!is_zero(a)){
        choice=m("u = "+txt(base));
        if (is_one(n)){ r=sym2(at_division,mul(p,sym1(at_ln,sym1(at_abs,base))),den(a)); label="Log rule"; return true; }
        const gen e=eval(1-n,1,contextptr);
        r=sym2(at_division,mul(p,pw(base,e)),den(eval(e*a,1,contextptr)));
        label="Power rule";
        return true;
      }
      // c/(w^2+k), k > 0, w linear: atan(w/sqrt(k))/(a*sqrt(k))
      if (is_op(q,at_plus) && args(q).size()==2){
        const vecteur t=args(q);
        for (int i=0;i<2;++i){
          const gen & sq=t[i], & k=t[1-i];
          if (!is_op(sq,at_pow) || !(args(sq)[1]==2) || !free_of(k,v) || !is_strictly_positive(k,contextptr)) continue;
          const gen w=args(sq)[0],a=w==v?gen(1):lin_coef(w,v);
          if (is_zero(a)) continue;
          const gen s=eval(sym1(at_sqrt,k),1,contextptr);
          r=sym2(at_division,mul(p,sym1(at_atan,sym2(at_division,w,s))),den(eval(a*s,1,contextptr)));
          label="Integral of 1/(u^2+a^2)";
          choice=m("a = "+txt(s));
          return true;
        }
      }
```

(then the existing `c/v, c/v^n, c/sqrt(v)` block continues). After the `at_pow && a[0]==v` rule add the linear power `(ax+b)^n`:

```cpp
  if (s==at_pow && free_of(a[1],v)){
    const gen c=lin_coef(a[0],v),e1=eval(a[1]+1,1,contextptr);
    if (!is_zero(c) && !is_zero(e1)){
      r=sym2(at_division,pw(a[0],e1),den(eval(e1*c,1,contextptr)));
      label="Power rule";
      choice=m("u = "+txt(a[0]));
      return true;
    }
  }
```

Before `r=table_int(...)` add Expand:

```cpp
  // a product or integer power of sums that is a polynomial: expanded, then term by term
  if ((s==at_prod || (s==at_pow && a[1].type==_INT_ && a[1].val>=2)) && contains(f,at_plus) && poly_v(f,v)){
    r=inode(gen(expand(eval(f,1,contextptr),contextptr).print(contextptr),contextptr),v);
    label="Expand";
    return true;
  }
```

- [ ] **Step 3: Host tests** — all pass; read `integrate(cos(3x),x)` (`Integral of cos`, choice `u = 3x: divide by 3`, `sin(3x)/3`), `integrate(3/((x+2)^2+9),x)` (`atan((x+2)/3)`).
- [ ] **Step 4: Build, size, commit** `Steps: integrals with a linear inner argument, 1/(u^2+a^2), Expand`.

---

### Task 2: Partial fractions

**Files:** Modify `src/steps.cc` (`pfrac`, `split_num`; `irule` calls them after `usub`), `tests/host/steps_cases.txt`.

**Interfaces:** Produces `static __attribute__((noinline)) bool pfrac(f,v,r,label,choice)` and `static __attribute__((noinline)) bool split_num(f,v,r,label,choice)`.

- [ ] **Step 1: Failing cases**

```text
integrate(1/(x^2-1),x) :: Partial fractions, Difference rule, Log rule, Log rule
integrate((x^3+1)/(x^2-1),x) :: Polynomial division, Sum rule, Power rule
integrate(1/(x*(x+1)^2),x) :: Partial fractions, Log rule, Power rule, Log rule
integrate((3x+5)/((x-1)*(x^2+1)),x) :: Partial fractions, Log rule, Split the numerator
integrate((x+4)/(x^2+4x+8),x) :: Split the numerator, u-substitution, Complete the square, Integral of 1/(u^2+a^2)
integrate(1/(4x^2-4x+3),x) :: Complete the square, Integral of 1/(u^2+a^2)
integrate(1/(x^3+x),x) :: Partial fractions
```

- [ ] **Step 2: Implement** (before `irule`):

```cpp
static gen deg_v(const gen & p,const gen & v){ return _degree(makesequence(p,v),contextptr); }
// a rational function of v: division first when not proper (Polynomial division), else the
// decomposition (Partial fractions); a lone irreducible quadratic below goes to split_num
static __attribute__((noinline)) bool pfrac(const gen & f,const gen & v,gen & r,string & label,string & choice){
  const gen e=eval(f,1,contextptr);
  const vecteur l=lvar(e);
  if (l.size()!=1 || !(l.front()==v)) return false;
  const gen N=_numer(e,contextptr),D=_denom(e,contextptr);
  if (free_of(D,v)) return false;
  const gen dn=deg_v(N,v),dd=deg_v(D,v);
  if (dn.type!=_INT_ || dd.type!=_INT_) return false;
  if (dn.val>=dd.val){
    const gen Q=_quo(makesequence(N,D,v),contextptr),R=_rem(makesequence(N,D,v),contextptr);
    const gen RD=gen(normal(R/D,contextptr).print(contextptr),contextptr);
    r=is_zero(R)?inode(Q,v):sym2(at_plus,inode(Q,v),inode(RD,v));
    label="Polynomial division";
    choice=m(txt(f)+" = "+txt(Q)+(is_zero(R)?string():" + "+txt(RD)));
    return true;
  }
  const gen P=gen(_partfrac(makesequence(e,v),contextptr).print(contextptr),contextptr);
  if (!is_op(P,at_plus) && !is_op(P,at_binary_minus)) return false; // one term: split_num, complete_square
  r=inode(P,v);
  label="Partial fractions";
  choice=m(txt(f)+" = "+txt(P));
  return true;
}
// (Bx+C)/Q, Q quadratic (a x^2+b x+c): (B/(2a)) Q'/Q + (C-B b/(2a))/Q, so the first is
// ln|Q| (u-substitution) and the second an arctangent; C'/Q alone: complete the square
static __attribute__((noinline)) bool split_num(const gen & f,const gen & v,gen & r,string & label,string & choice){
  const gen e=eval(f,1,contextptr),N=_numer(e,contextptr),Q=_denom(e,contextptr);
  const gen dq=deg_v(Q,v),dn=deg_v(N,v);
  if (dq.type!=_INT_ || dq.val!=2 || dn.type!=_INT_ || dn.val>1) return false;
  const gen dQ=derive(Q,v,contextptr);
  if (dn.val==0){ // C/Q: Q = a((x+h)^2+k)
    const gen S=gen(_canonical_form(makesequence(Q,v),contextptr).print(contextptr),contextptr);
    if (S==Q) return false;
    r=inode(sym2(at_division,N,S),v);
    label="Complete the square";
    choice=m(txt(Q)+" = "+txt(S));
    return true;
  }
  const gen B=_coeff(makesequence(N,v,1),contextptr),k=normal(B/_coeff(makesequence(dQ,v,1),contextptr),contextptr);
  const gen C2=normal(N-k*dQ,contextptr);
  r=sym2(at_plus,mul(k,inode(sym2(at_division,dQ,Q),v)),inode(sym2(at_division,C2,Q),v));
  label="Split the numerator";
  choice=m(txt(N)+" = "+txt(k)+"*("+txt(dQ)+") + "+txt(C2));
  return true;
}
```

In `irule`, the last line becomes `return usub(f,v,r,label,choice,pre) || pfrac(f,v,r,label,choice) || split_num(f,v,r,label,choice) || parts(f,v,r,label,choice);`.

Notes: `_numer`, `_denom`, `_quo`, `_rem`, `_partfrac`, `_degree`, `_coeff`, `_canonical_form` are giac commands (check each name in `src/giac/*.h`; `_coeff` may be `_coeffs`: use what exists, `grep -n "gen _coeff\|gen _canonical_form\|gen _quo\|gen _rem" src/giac/*.h`). A `0*` term from `split_num` (C2 = 0) is dropped by `mul`/`add` if built with them: build `r` with `add(makevecteur(...))` and `is_zero(C2)` → only the first term.

- [ ] **Step 3: Host tests** — all pass; read the traces (the `(x+4)/(x^2+4x+8)` trace ends `ln|x^2+4x+8|/2 + atan((x+2)/2)`).
- [ ] **Step 4: Build, size, commit** `Steps: partial fractions (division, decomposition, splitting the numerator, completing the square)`.

---

### Task 3: Trig integrals

**Files:** Modify `src/steps.cc` (`sincos`, `trig_rewrite`; `irule` calls `trig_rewrite` before `usub`; `TABLE` gains sec³), tests.

**Interfaces:** Produces `static bool sincos(f,v,c,w,m,n)` (f = c sin(w)^m cos(w)^n, w linear, m, n ≥ 0) and `static __attribute__((noinline)) bool trig_rewrite(f,v,r,label,choice)`.

- [ ] **Step 1: Failing cases**

```text
integrate(sin(x)^3,x) :: Pythagorean identity, u-substitution, Expand, Substitute back
integrate(sin(x)^2*cos(x)^3,x) :: Pythagorean identity, u-substitution, Substitute back
integrate(sin(x)^2,x) :: Power-reducing identity, Difference rule, Integral of cos
integrate(sin(x)^2*cos(x)^2,x) :: Power-reducing identity
integrate(cos(2x)^2,x) :: Power-reducing identity
integrate(tan(x)^3,x) :: Pythagorean identity, Difference rule, u-substitution, Substitute back, Integral of tan
integrate(tan(x)^2,x) :: Pythagorean identity, Difference rule, Integral of sec^2, Constant rule
integrate(sec(x)^3,x) :: Integral of sec^3
integrate(sin(x^2)^3,x) :: NONE
```

- [ ] **Step 2: Implement**

Add to `TABLE` (before the `1/(1+x^2)` entries): `"sec^3","sec(x)^3","(sec(x)*tan(x)+ln(abs(sec(x)+tan(x))))/2",`.

Before `irule`:

```cpp
// f = c*sin(w)^m*cos(w)^n (products, powers; w linear in v; m, n >= 0)
static bool sincos(const gen & f,const gen & v,gen & c,gen & w,int & m,int & n){
  if (free_of(f,v)){ c=c*f; return true; }
  if (is_op(f,at_prod)){
    const vecteur a=args(f);
    for (unsigned i=0;i<a.size();++i) if (!sincos(a[i],v,c,w,m,n)) return false;
    return true;
  }
  int e=1;
  gen b=f;
  if (is_op(f,at_pow) && args(f)[1].type==_INT_ && args(f)[1].val>0){ e=args(f)[1].val; b=args(f)[0]; }
  if (!is_op(b,at_sin) && !is_op(b,at_cos)) return false;
  const gen a=b._SYMBptr->feuille;
  if ((!is_zero(w) && !(a==w)) || (!(a==v) && is_zero(lin_coef(a,v)))) return false;
  w=a;
  (is_op(b,at_sin)?m:n)+=e;
  return true;
}
// trig integrals: an odd power keeps one factor and turns the rest by sin^2 + cos^2 = 1 (then a
// u-substitution); even powers of both: the power-reducing identities (tlin); tan^n (n >= 2):
// tan^(n-2)*(sec^2 - 1)
static __attribute__((noinline)) bool trig_rewrite(const gen & f,const gen & v,gen & r,string & label,string & choice){
  if (is_op(f,at_pow) && is_op(args(f)[0],at_tan) && args(f)[1].type==_INT_ && args(f)[1].val>=2){
    const gen t=args(f)[0],w=t._SYMBptr->feuille,k=args(f)[1].val-2,s2=sym2(at_pow,sym1(at_sec,w),2);
    if (!(w==v) && is_zero(lin_coef(w,v))) return false;
    r=inode(sym2(at_binary_minus,mul(pw(t,k),s2),pw(t,k)),v);
    label="Pythagorean identity";
    choice=m(txt(sym2(at_pow,t,2))+" = "+txt(s2)+"-1");
    return true;
  }
  gen c=1,w=0;
  int M=0,N=0;
  if (!sincos(f,v,c,w,M,N) || M+N<2) return false;
  const gen S=sym1(at_sin,w),C=sym1(at_cos,w);
  if (M%2 || N%2){ // keep one factor of the odd power (sin first: u = cos)
    const bool s=M%2;
    const gen keep=s?S:C,other=s?C:S;
    const int o=(s?M:N)-1;
    const gen id=sym2(at_binary_minus,1,sym2(at_pow,other,2)); // 1 - cos^2 (or 1 - sin^2)
    r=inode(mul(mul(c,pw(id,o/2)),mul(pw(other,s?N:M),keep)),v);
    label="Pythagorean identity";
    choice=m(txt(sym2(at_pow,keep,2))+" = "+txt(id));
    return true;
  }
  r=inode(gen(_tlin(eval(f,1,contextptr),contextptr).print(contextptr),contextptr),v);
  label="Power-reducing identity";
  choice=m("sin(u)^2 = (1-cos(2*u))/2")+", "+m("cos(u)^2 = (1+cos(2*u))/2");
  return true;
}
```

In `irule`, before `r=table_int(...)`: `if (trig_rewrite(f,v,r,label,choice)) return true;` — but only when the table does not know f (sec^3 is in the table; `sin(x)^1` is not a rewrite since M+N<2). Order: `table_int` first, then `trig_rewrite`, then `usub`... Write it as: `r=table_int(f,v,label,choice); if (!is_zero(r)) return true; if (trig_rewrite(f,v,r,label,choice)) return true;`.

Watch for loops: after the odd rewrite, `usub` with u = cos (or sin) must take the expression (candidates include the function itself, part 2a fix). Then the inner integral is a polynomial in u: `Expand` (Task 1) when it is a product/power of sums.

- [ ] **Step 3: Host tests** — all pass; read `sin(x)^3` (→ `(1-cos(x)^2)*sin(x)`, u = cos x, `-∫(1-u^2)du`... `cos(x)^3/3 - cos(x)`).
- [ ] **Step 4: Build, size, commit** `Steps: trig integrals (Pythagorean identity, power reduction, powers of tan, sec^3)`.

---

### Task 4: Trig substitution

**Files:** Modify `src/steps.cc` (`trig_sub`; `irule` calls it after `usub`, before `pfrac`), tests.

**Interfaces:** Produces `static __attribute__((noinline)) bool trig_sub(f,v,r,label,choice,pre)`.

- [ ] **Step 1: Failing cases**

```text
integrate(sqrt(9-x^2),x) :: Trig substitution, Power-reducing identity, Back-substitute :: `x = 3*sin(t)`
integrate(1/(x^2*sqrt(x^2+4)),x) :: Trig substitution, Back-substitute :: `x = 2*tan(t)`
integrate(sqrt(x^2-4)/x,x) :: Trig substitution, Back-substitute :: `x = 2*sec(t)`
integrate(x^3/sqrt(4-x^2),x) :: Trig substitution, Back-substitute
integrate(sqrt(x^2+2x),x) :: NONE
```

- [ ] **Step 2: Implement** (before `irule`; `itrace` is declared above):

```cpp
// trig substitution for sqrt(a^2-x^2) (x = a sin t), sqrt(x^2+a^2) (x = a tan t), sqrt(x^2-a^2)
// (x = a sec t): the integral in t traced on its own (pre), then back-substituted by the triangle
static __attribute__((noinline)) bool trig_sub(const gen & f,const gen & v,gen & r,string & label,string & choice,vector<step> & pre){
  const vecteur roots=lop(f,at_sqrt);
  if (roots.size()!=1) return false;
  const gen R=eval(args(roots[0])[0],1,contextptr),v2=v*v;
  const gen k=normal(R-v2,contextptr),k2=normal(R+v2,contextptr); // R = v^2+k, or R = k2-v^2
  int kind;
  gen a2;
  if (free_of(k2,v) && is_strictly_positive(k2,contextptr) && equal(R,k2-v2)){ kind=0; a2=k2; }   // a^2-x^2
  else if (free_of(k,v) && is_strictly_positive(k,contextptr)){ kind=1; a2=k; }                  // x^2+a^2
  else if (free_of(k,v) && is_strictly_positive(-k,contextptr)){ kind=2; a2=-k; }                // x^2-a^2
  else return false;
  const gen t=free_var(f); // ("t" when free: u, w, t, s: the first free)
  if (is_zero(t)) return false;
  const gen a=eval(sym1(at_sqrt,a2),1,contextptr);
  // x = a sin t, a tan t, a sec t; dx; the root as a cos t, a sec t, a tan t (t in the usual range)
  static const char * const X[]={"a*sin(t)","a*tan(t)","a*sec(t)"},* const DX[]={"a*cos(t)","a*sec(t)^2","a*sec(t)*tan(t)"},* const RT[]={"a*cos(t)","a*sec(t)","a*tan(t)"};
  const gen ga("a",contextptr),gt("t",contextptr);
  const gen xs=quotesubst(quotesubst(gen(X[kind],contextptr),ga,a,contextptr),gt,t,contextptr);
  const gen dx=quotesubst(quotesubst(gen(DX[kind],contextptr),ga,a,contextptr),gt,t,contextptr);
  const gen rt=quotesubst(quotesubst(gen(RT[kind],contextptr),ga,a,contextptr),gt,t,contextptr);
  const gen G0=normal(eval(subst(quotesubst(f,roots[0],rt,contextptr),v,xs,false,contextptr)*dx,1,contextptr),contextptr);
  if (!free_of(G0,v) || interrupted) return false;
  const gen G(G0.print(contextptr),contextptr);
  const size_t n0=pre.size();
  step s={"Trig substitution",m(txt(v)+" = "+txt(xs))+", "+m(txt(dvar(v))+" = "+txt(mul(dx,dvar(t))))+"\n"+m(txt(roots[0])+" = "+txt(rt)),txt(inode(G,t))};
  pre.push_back(s);
  gen Et=inode(G,t);
  ++usub_depth;
  const int kk=itrace(Et,G,t,pre);
  --usub_depth;
  if (kk!=STEPS_OK){ pre.resize(n0); return false; }
  // back: sin 2t = 2 sin t cos t first (texpand), then the triangle, then t itself
  static const char * const B[]={"x/a","sqrt(a^2-x^2)/a","x/sqrt(a^2-x^2)","asin(x/a)",  // sin, cos, tan, t
                                 "x/sqrt(x^2+a^2)","a/sqrt(x^2+a^2)","x/a","atan(x/a)",
                                 "sqrt(x^2-a^2)/x","a/x","sqrt(x^2-a^2)/a","acos(a/x)"};
  const gen gx("x",contextptr);
  gen F=_texpand(eval(Et,1,contextptr),contextptr);
  const unary_function_ptr * const fs[]={at_sin,at_cos,at_tan};
  vecteur from,to;
  for (int i=0;i<3;++i){
    from.push_back(symbolic(fs[i],t));
    to.push_back(quotesubst(quotesubst(gen(B[4*kind+i],contextptr),ga,a,contextptr),gx,v,contextptr));
  }
  F=subst(F,from,to,false,contextptr);
  F=subst(F,t,quotesubst(quotesubst(gen(B[4*kind+3],contextptr),ga,a,contextptr),gx,v,contextptr),false,contextptr);
  r=gen(normal(F,contextptr).print(contextptr),contextptr);
  label="Back-substitute";
  choice=m(txt(from[0])+" = "+txt(to[0]))+", "+m(txt(from[1])+" = "+txt(to[1]));
  return true;
}
```

In `irule`, the last line becomes `return usub(...) || trig_sub(f,v,r,label,choice,pre) || pfrac(...) || split_num(...) || parts(...);`.

Notes: sec(t) and other functions of t left after `texpand` (sec, csc, cot) are rewritten first: if `F` contains `at_sec` etc., apply `_tan2sincos` / rewrite sec = 1/cos (`subst` with `1/cos(t)`) before the triangle. If the outer check fails (a branch of |cos t| the textbook ignores), the trace is discarded: "No steps".

- [ ] **Step 3: Host tests** — all pass; read `sqrt(9-x^2)` (`x = 3 sin t`, `∫9cos(t)^2 dt`, power reduction, `sin(2t)` → `2 sin t cos t`, back to `x sqrt(9-x^2)/2 + 9 asin(x/3)/2`).
- [ ] **Step 4: Build, size, commit** `Steps: trig substitution (sin, tan, sec) with the back-substitution by the triangle`.

---

### Task 5: On the calculator, review

- [ ] Emulator screenshots: `1/(x^2-1)`, `(x+4)/(x^2+4x+8)`, `sin(x)^3`, `sin(x)^2`, `sqrt(9-x^2)` (all their scroll positions; typed as `integrate(...,x)` text or with the template, checking the typed screenshot).
- [ ] Emulator suite (715): SAME. Host steps tests: all pass.
- [ ] Bundle `FlowCE.b84`, `site/build.sh ... v1.9-steps.4`.
- [ ] Final review (fresh reviewer, Opus), fixes RED→GREEN, ledger.
