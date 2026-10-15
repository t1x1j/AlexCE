# Steps, part 1 (groundwork + derivatives) Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** `2nd` `F4` on a derivative's answer opens a Steps screen with textbook steps (rule, choice, 2D expression), every step checked by giac; Python syntax removed to make room.

**Architecture:** `src/steps.cc` re-solves `diff(f,x[,n])` by expanding unevaluated `diff` nodes one rule at a time on giac's unevaluated parse tree, checking each step with `simplify(eval(step) - derivative) == 0`. `src/focus_steps.cc` draws the list with the existing 2D layout (`ui_math_fit`/`ui_math_draw`). `main.cc` (`console_show_steps`) runs the trace with ON/out-of-memory handling like the F4 forms; `console.cc` routes `2nd` `F4` (`KEY_CTRL_F9`) there.

**Tech Stack:** C++14 for the CE toolchain (CEdev v14.2, eZ80, uSTL as `std`), giac (KhiCAS fork), WSL build, CEmu headless, host build `tools/hostgiac`.

**Spec:** `docs/superpowers/specs/2026-10-14-steps-design.md` (integrals and limits are later plans).

## Global Constraints

- The app must fit in 43 flash pages: `_DEMO.bin` at most 2,818,045 B (`wsl_build.sh` checks; a 44th AppIns needs at least 1 KB in it).
- Giac's engine sources (`src/giac/`) are not modified, except the one Python-syntax switch in Task 1.
- No regression on the emulator suite versus `$KB/results/baseline_v1.9.txt.diff` (715 problems: 28 differ, 31 slow, 6 timed out, 0 hung): no new DIFF, TIMEOUT or HANG lines.
- A wrong step is never shown: any failed check discards the whole trace ("No steps for this one. The answer is still correct.").
- Steps are computed only on `2nd` `F4`; the normal answer path (`do_run`, `answer.cc`) is unchanged.
- `2nd` `F4` keeps its current menu (polynomials) whenever the selected result is not a derivative.
- Commit messages carry no attribution lines; each commit is pushed to `origin steps`.
- Build commands (Git Bash, repo root): `FLOWCE_WSL_DISTRO=Ubuntu KB=/home/toadvine/flowce-build tools/dev/build.sh en`. WSL commands go through a script file (`wsl.exe` drops `$VAR` in inline commands): write the script to the scratchpad and run `MSYS_NO_PATHCONV=1 wsl.exe -d Ubuntu -- bash <script path in /mnt/c/...>`.
- Host build: in WSL, `KB=~/flowce-build HG_BUILD=~/flowce-build/hostgiac bash /mnt/c/Users/Strad/Desktop/Folder/FlowCE-Steps/tools/hostgiac/build.sh worktree` → `~/flowce-build/hostgiac/bin/hostgiac-worktree`.

## Review Focus

- A derivative with another variable (`diff(t^2*sin(t),t)`): steps use t, not x (test in Task 2's cases).
- A function the tracer does not know (`diff(f(x),x)`, `diff(floor(x),x)`): "No steps", no crash (Task 3's cases).
- A long expression (a product of 6 factors): every expression still drawn (the layout shrinks), at most `STEPS_MAX` steps, else "No steps" (Task 3's cases, Task 4's screenshots).
- ON pressed during a slow trace: "Stopped", and the console keeps working (Task 4, step "ON").
- `2nd` `F4` on a result that is not a derivative (an integral, `factor(x^2-1)`), or with nothing selected: the polynomial menu as before (Task 4 screenshots).

---

### Task 1: Drop Python syntax (28.4 KB)

**Files:**
- Modify: `src/giac/kglobal.cc:2908` (the `#if` before `python2xcas`)
- Modify: `makefile:16-24` (FEATURE_DEFS)

**Interfaces:**
- Produces: the `NO_PYTHON_SYNTAX` define (default build); `python2xcas` returns its input unchanged.

- [ ] **Step 1: Record the size before**

Baseline (already measured on `c32720d`): `_DEMO.bin=2794188 B`, room 23,857 B.

- [ ] **Step 2: Switch the translator off when `NO_PYTHON_SYNTAX` is defined**

In `src/giac/kglobal.cc`, replace

```cpp
#if defined FLOWCE && defined WITH_UNITS // FlowCE with units has no Python syntax: input is never
  // translated (python2xcas is 28 KB: units and Python do not both fit)
```

with

```cpp
#if defined FLOWCE && (defined WITH_UNITS || defined NO_PYTHON_SYNTAX) // FlowCE with units, or
  // with the steps (NO_PYTHON_SYNTAX: the room they need), has no Python syntax: input is never
  // translated (python2xcas is 28 KB)
```

- [ ] **Step 3: Define it in the default build**

In `makefile`, replace

```make
FEATURE_DEFS = -DWITH_LAPLACE -DWITH_DESOLVE -DWITH_EQW -DWITH_PLOT
ifeq ($(UNITS),1)
    FEATURE_DEFS += -DWITH_UNITS
endif
```

with

```make
FEATURE_DEFS = -DWITH_LAPLACE -DWITH_DESOLVE -DWITH_EQW -DWITH_PLOT
ifeq ($(UNITS),1)
    FEATURE_DEFS += -DWITH_UNITS
else
    # FlowCE Steps: giac's Python syntax (28.4 KB) gives its room to the worked steps (steps.cc)
    FEATURE_DEFS += -DNO_PYTHON_SYNTAX
endif
```

- [ ] **Step 4: Build and measure**

Run: `FLOWCE_WSL_DISTRO=Ubuntu KB=/home/toadvine/flowce-build tools/dev/build.sh en`
Expected: `[build] OK ... _DEMO.bin=` about 2,765,800 B, `room left:` about 52,000 B. Write the exact numbers into the commit message.

- [ ] **Step 5: Install into the emulator and run the suite**

WSL script:

```bash
export KB=~/flowce-build KHICAS_ROM=~/flowce-build/emu/rom/TI84CE.rom
R=/mnt/c/Users/Strad/Desktop/Folder/FlowCE-Steps; H=$R/tools/hostgiac
python3 $R/tools/emu/install.py en base $KB/emu/shots 2>&1 | grep -v 'screen size is bogus'
python3 $R/tools/emu/batch.py base $KB/results/nopython.txt $H/corpus_calc1_web.txt $H/corpus_calc23.txt $H/corpus_calc23_web.txt -b $KB/hostgiac/bin/hostgiac-worktree > $KB/logs/nopython.log 2>&1
tail -1 $KB/results/nopython.txt.diff
diff <(grep -E '^(DIFF|TIMEOUT|HANG)' $KB/results/baseline_v1.9.txt.diff) <(grep -E '^(DIFF|TIMEOUT|HANG)' $KB/results/nopython.txt.diff) && echo SAME
```

Expected: `installed 43 AppIns`, then the summary line, then `SAME` (no new DIFF/TIMEOUT/HANG lines). Takes about 10 minutes; run in the background.

- [ ] **Step 6: Commit**

```bash
git add src/giac/kglobal.cc makefile
git commit -m "Drop Python syntax (NO_PYTHON_SYNTAX): room for the steps

_DEMO.bin <before> -> <after> B, room <after room> B. Emulator suite (715 problems): no new
differences, timeouts or hangs."
git push -q origin steps
```

---

### Task 2: Derivative tracer core (sum, constant, power) and host tests

**Files:**
- Create: `src/steps.h`, `src/steps.cc`
- Create: `tests/host/steps_cases.txt`, `tests/host/check_steps.py`, `tests/host/run_steps_tests.sh`
- Modify: `tools/hostgiac/khicas_post.cc` (add `khicas_steps`), `tools/hostgiac/driver.cc` (`-S`), `tools/hostgiac/Makefile:22` (HOST_EXTRA)

**Interfaces:**
- Produces (`src/steps.h`):

```cpp
struct step { std::string label, choice, expr; };
enum { STEPS_OK, STEPS_NONE, STEPS_STOPPED };
enum { STEPS_MAX = 40 };
int steps_applicable(const char * input);
int steps_build(const char * input,const std::string & answer,std::string & problem,std::vector<step> & out);
```

- [ ] **Step 1: Write the test cases (labels expected in order)**

`tests/host/steps_cases.txt` (one problem per line: `input :: expected labels, comma separated` or `:: NONE`):

```text
# Steps of derivatives (steps.cc): the labels expected, in order (others, e.g. a final Simplify, may follow)
diff(x^3+5x,x) :: Sum rule, Power rule
diff(4x^5,x) :: Constant multiple rule, Power rule
diff(x^3-x^2,x) :: Difference rule, Power rule, Power rule
diff(7,x) :: Constant rule
diff(3x+2,x) :: Linear function
diff(t^4+t,t) :: Sum rule, Power rule
```

- [ ] **Step 2: Write the checker**

`tests/host/check_steps.py`:

```python
#!/usr/bin/env python3
"""Checks hostgiac -k -S -p output against tests/host/steps_cases.txt.
Usage: check_steps.py <cases> <output>. Each case: its labels must appear in order among the
problem's [label] lines (a final [Simplify] may follow), or ':: NONE' expects '(no steps)'.
'(stopped)' always fails. Exit 1 on any failure."""
import re, sys

cases = []
for line in open(sys.argv[1], encoding='utf-8'):
    line = line.strip()
    if not line or line.startswith('#'):
        continue
    inp, _, exp = line.partition(' :: ')
    cases.append((inp.strip(), [e.strip() for e in exp.split(',') if e.strip()]))

out = open(sys.argv[2], encoding='utf-8').read().split('\n')
blocks, cur = {}, None
for l in out:
    m = re.match(r'^(\S.*?) -> ', l)
    if m and not l.startswith('  '):
        cur = m.group(1)
        blocks[cur] = [l]
    elif cur is not None:
        blocks[cur].append(l)

bad = 0
for inp, exp in cases:
    b = blocks.get(inp)
    if b is None:
        print('MISSING', inp); bad += 1; continue
    text = '\n'.join(b)
    if '(stopped)' in text:
        print('STOPPED', inp); bad += 1; continue
    if exp == ['NONE']:
        if '(no steps)' not in text:
            print('EXPECTED NONE', inp, '\n' + text); bad += 1
        continue
    if '(no steps)' in text:
        print('NO STEPS', inp, '\n' + text); bad += 1; continue
    labels = re.findall(r'^  \[([^\]]+)\]', text, re.M)
    i = 0
    for lab in labels:
        if i < len(exp) and lab == exp[i]:
            i += 1
    if i < len(exp):
        print('LABELS', inp, 'expected', exp, 'got', labels); bad += 1
print(f'{len(cases) - bad}/{len(cases)} cases pass')
sys.exit(1 if bad else 0)
```

`tests/host/run_steps_tests.sh`:

```bash
#!/bin/bash
# Host tests of the steps (steps.cc): builds tools/hostgiac (worktree), prints the steps of
# tests/host/steps_cases.txt and checks their labels. Usage (WSL): run_steps_tests.sh
set -e
T=$(cd "$(dirname "$0")" && pwd); R=$(cd "$T/../.." && pwd)
export HG_BUILD=${HG_BUILD:-$HOME/flowce-build/hostgiac}
bash "$R/tools/hostgiac/build.sh" worktree > /tmp/steps_build.log 2>&1 || { tail -30 /tmp/steps_build.log; exit 1; }
cut -d: -f1 "$T/steps_cases.txt" | sed 's/ *$//' | grep -v '^#' | grep -v '^$' > /tmp/steps_inputs.txt
"$HG_BUILD/bin/hostgiac-worktree" -k -S -p -f /tmp/steps_inputs.txt > /tmp/steps_out.txt 2>&1
cat /tmp/steps_out.txt
python3 "$T/check_steps.py" "$T/steps_cases.txt" /tmp/steps_out.txt
```

Note: `cut -d: -f1` splits at the first `:`; inputs never contain `:`.

- [ ] **Step 3: Wire `-S` into the host driver**

`tools/hostgiac/Makefile`, line `HOST_EXTRA := ...`: append `$(OBJ)/khicas/steps.o`:

```make
HOST_EXTRA := $(OBJ)/host/stubs_ui.o $(OBJ)/host/khicas_post.o $(OBJ)/khicas/answer.o $(OBJ)/khicas/steps.o
```

`tools/hostgiac/driver.cc`: in the option comment block after `-F`, add

```cpp
//   -S       with -k: the answer, then its worked steps (src/steps.cc), one "  [rule] choice :: expr" line each
```

next to the other weak declarations add

```cpp
std::string khicas_steps(const char * s) __attribute__((weak)); // -S: the answer and its steps
```

in `main`, add the flag `steps=false` to the `bool` list, the option `else if (!strcmp(argv[i],"-S")) steps=true;`, and change the evaluation line to

```cpp
      const std::string res=dorun?(forms?khicas_forms(exprs[k]):steps?khicas_steps(exprs[k]):khicas_do_run(exprs[k])):eval_one(exprs[k],autosimp,prepass);
```

`tools/hostgiac/khicas_post.cc`: add `#include "../../src/steps.h"` after the `answer.h` include, and at the end of the file:

```cpp
// -S: the worked steps of the answer (steps.cc), as 2nd F4 shows them:
// "answer\n  problem: ...\n  [rule] choice :: expr" (or "  (no steps)", "  (stopped)")
std::string khicas_steps(const char * s){
  std::string printed=khicas_do_run(s);
  const size_t a=printed.find("  ~ ");
  const std::string bare=a==std::string::npos?printed:printed.substr(0,a);
  std::string problem;
  std::vector<step> v;
  const int r=steps_build(s,bare,problem,v);
  std::string out=bare+"\n  problem: "+problem;
  if (r==STEPS_NONE) out+="\n  (no steps)";
  if (r==STEPS_STOPPED) out+="\n  (stopped)";
  for (size_t i=0;i<v.size();++i){
    out+="\n  ["+v[i].label+"]";
    if (!v[i].choice.empty()) out+=" "+v[i].choice;
    out+=" :: "+v[i].expr;
  }
  ctrl_c=kbd_interrupted=interrupted=false;
  return out;
}
```

- [ ] **Step 4: Run the tests to see them fail**

Run (WSL): `bash /mnt/c/Users/Strad/Desktop/Folder/FlowCE-Steps/tests/host/run_steps_tests.sh`
Expected: the host build fails (`steps.h: No such file`), which is the failing state.

- [ ] **Step 5: Write `src/steps.h`**

```cpp
// steps.h - worked steps (steps.cc): a derivative re-solved one textbook rule at a time, each
// step checked by giac. 2nd F4 on the result shows them (main.cc console_show_steps,
// focus_steps.cc). tools/hostgiac's -S option prints them.
#ifndef STEPS_H
#define STEPS_H
#include <giac/giacPCH.h>

struct step {
  std::string label;  // the rule: "Product rule", "Chain rule", "Simplify"
  std::string choice; // what was chosen ("f = x^2, g = sin(3x)"), or empty
  std::string expr;   // the whole expression after the step, in textbook notation
};
enum { STEPS_OK, STEPS_NONE, STEPS_STOPPED };
enum { STEPS_MAX = 40 }; // more steps: no steps (RAM, and no textbook writes 40)

// the typed text of a calculation is one steps explain (diff(...)): 2nd F4 shows them
int steps_applicable(const char * input);
// the steps of input (the typed text) whose answer FlowCE printed as answer; problem gets the
// problem in textbook notation. STEPS_NONE: no textbook explanation, or a check failed (out is
// empty then); STEPS_STOPPED: interrupted (ON, out of memory)
int steps_build(const char * input,const std::string & answer,std::string & problem,std::vector<step> & out);
#endif
```

- [ ] **Step 6: Write `src/steps.cc` with the core rules**

```cpp
// steps.cc - worked steps (steps.h). The typed problem is parsed without being evaluated (giac
// keeps sec, sqrt, a/b as typed), then its unevaluated diff(u,x) nodes are expanded one rule at a
// time, outermost and leftmost first: each expansion is one step. Derivatives a reader sees at
// once (a constant, x, a linear ax+b) are written directly. After each step the expression is
// evaluated and compared with giac's derivative: a step that does not check discards the trace.
#include <string.h>
#include <stdlib.h>
#include <time.h> // (before giac: first.h defines a clock macro)
#include "steps.h"
#include "answer.h"

using namespace std;
using namespace giac;
extern giac::context * contextptr;

// out of line: each inline symbolic(...) is about 100 bytes of eZ80 code (answer.cc's sym1, sym2)
static __attribute__((noinline)) gen sym1(const unary_function_ptr * o,const gen & a){
  return symbolic(o,a);
}
static __attribute__((noinline)) gen sym2(const unary_function_ptr * o,const gen & a,const gen & b){
  return symbolic(o,makesequence(a,b));
}
static bool free_of(const gen & e,const gen & x){ return !contains(e,x); }
static bool is_op(const gen & g,const unary_function_ptr * o){
  return g.type==_SYMB && g._SYMBptr->sommet==o;
}
// the arguments of a symbolic g: one for a function, several for + * / -
static vecteur args(const gen & g){
  const gen & f=g._SYMBptr->feuille;
  return f.type==_VECT?*f._VECTptr:vecteur(1,f);
}
// a*b, a+b+..., -a with only what a reader would not write dropped (0 and 1); no simplification
static gen mul(const gen & a,const gen & b){
  if (is_zero(a) || is_zero(b)) return 0;
  if (is_one(a)) return b;
  if (is_one(b)) return a;
  return sym2(at_prod,a,b);
}
static gen neg(const gen & a){ return is_zero(a)?gen(0):sym1(at_neg,a); }
static gen add(const vecteur & v){
  vecteur w;
  for (unsigned i=0;i<v.size();++i)
    if (!is_zero(v[i])) w.push_back(v[i]);
  if (w.empty()) return 0;
  return w.size()==1?w[0]:symbolic(at_plus,gen(w,_SEQ__VECT));
}
static gen prod(const vecteur & v){ return v.size()==1?v[0]:symbolic(at_prod,gen(v,_SEQ__VECT)); }
static gen pw(const gen & a,const gen & n){ return is_one(n)?a:is_zero(n)?gen(1):sym2(at_pow,a,n); }
// g as FlowCE prints answers (the textbook notation of answer.cc)
static string txt(const gen & g){
  string s=g.print(contextptr);
  textbook(s);
  return s;
}

static gen dnode(const gen & u,const gen & x){ return sym2(at_diff,u,x); }
// d/dx u written directly when a reader sees it at once (0, 1, a of ax+b), else left as diff(u,x)
static gen D(const gen & u,const gen & x){
  if (free_of(u,x)) return 0;
  if (u==x) return 1;
  gen a,b;
  if (is_linear_wrt(u,x,a,b,contextptr) && free_of(a,x)) return eval(a,1,contextptr);
  return dnode(u,x);
}

// one rule applied to d/dx u: its result r, the rule's name and what was chosen; false: no rule
static bool rule(const gen & u,const gen & x,gen & r,string & label,string & choice){
  choice.clear();
  if (u.type!=_SYMB) return false;
  const unary_function_ptr & s=u._SYMBptr->sommet;
  const vecteur v=args(u);
  if (s==at_plus || s==at_binary_minus){
    vecteur t;
    for (unsigned i=0;i<v.size();++i)
      t.push_back(s==at_binary_minus && i?neg(D(v[i],x)):D(v[i],x));
    r=add(t);
    label=s==at_binary_minus?"Difference rule":"Sum rule";
    return true;
  }
  if (s==at_neg){
    r=neg(D(v[0],x));
    label="Constant multiple rule";
    return true;
  }
  if (s==at_prod){
    vecteur c,f; // the constant factors, the others
    for (unsigned i=0;i<v.size();++i)
      (free_of(v[i],x)?c:f).push_back(v[i]);
    if (f.empty() || c.empty()) return false; // (products of several x factors: Task 3)
    r=mul(prod(c),D(prod(f),x));
    label="Constant multiple rule";
    return true;
  }
  if (s==at_pow && free_of(v[1],x) && v[0]==x){
    const gen m=eval(v[1]-1,1,contextptr);
    r=mul(v[1],pw(x,m));
    label="Power rule";
    return true;
  }
  return false;
}

// the first diff(u,x) of g (outermost, leftmost first) replaced by its rule: 1 done, 0 no node
// left, -1 a node no rule explains
static int expand(gen & g,const gen & x,string & label,string & choice){
  if (g.type!=_SYMB) return 0;
  if (g._SYMBptr->sommet==at_diff){
    gen r;
    if (!rule(args(g)[0],x,r,label,choice)) return -1;
    g=r;
    return 1;
  }
  vecteur v=args(g);
  for (unsigned i=0;i<v.size();++i){
    const int k=expand(v[i],x,label,choice);
    if (!k) continue;
    if (k>0){
      const gen & f=g._SYMBptr->feuille;
      g=symbolic(g._SYMBptr->sommet,f.type==_VECT?gen(v,f.subtype):v[0]);
    }
    return k;
  }
  return 0;
}

// g (its diff nodes evaluated) equals the derivative d
static bool same(const gen & g,const gen & d){
  const gen e=eval(g,1,contextptr);
  return !interrupted && is_zero(simplify(e-d,contextptr),contextptr);
}

int steps_applicable(const char * s){
  while (*s==' ') ++s;
  return !strncmp(s,"diff(",5);
}

int steps_build(const char * input,const string & answer,string & problem,vector<step> & out){
  out.clear();
  problem.clear();
  const int S=strlen(input),cap=2*S+32>256?2*S+32:256;
  char * buf=(char *)malloc(cap);
  if (!buf) return STEPS_STOPPED;
  strcpy(buf,input);
  answer_prepass(buf,cap,true); // as do_run: 2x is 2*x, Focus's log is log10
  const gen in(buf,contextptr);
  free(buf);
  if (!is_op(in,at_diff)) return STEPS_NONE;
  const vecteur a=args(in);
  if (a.size()<2 || a.size()>3 || a[1].type!=_IDNT) return STEPS_NONE;
  const gen x=a[1];
  const int n=a.size()==3?(a[2].type==_INT_?a[2].val:0):1;
  if (n<1 || n>3) return STEPS_NONE;
  problem=txt(in);
  gen f=a[0];
  for (int k=1;k<=n;++k){
    if (k>1){
      step s={"Differentiate again",k==2?"the second derivative":"the third derivative",txt(dnode(f,x))};
      out.push_back(s);
    }
    const gen d=derive(eval(f,1,contextptr),x,contextptr); // giac's derivative: each step must equal it
    gen g=D(f,x);
    if (!is_op(g,at_diff)){ // a constant or linear function: one step
      step s={is_zero(g)?"Constant rule":"Linear function","",txt(g)};
      out.push_back(s);
    }
    for (;;){
      string label,choice;
      const int r=expand(g,x,label,choice);
      if (interrupted){ out.clear(); return STEPS_STOPPED; }
      if (!r) break;
      if (r<0 || out.size()>=STEPS_MAX || !same(g,d)){
        out.clear();
        return interrupted?STEPS_STOPPED:STEPS_NONE;
      }
      step s={label,choice,txt(g)};
      out.push_back(s);
    }
    f=simplify(eval(g,1,contextptr),contextptr); // no diff left: the derivative, simplified
    if (k<n){
      step s={"Simplify","",txt(f)};
      out.push_back(s);
    }
  }
  // the last step is the answer as FlowCE shows it, which must be what the steps found
  const gen A=eval(gen(answer,contextptr),1,contextptr);
  if (interrupted){ out.clear(); return STEPS_STOPPED; }
  if (!is_zero(simplify(f-A,contextptr),contextptr)){ out.clear(); return STEPS_NONE; }
  if (out.empty() || out.back().expr!=answer){
    step s={"Simplify","",answer};
    out.push_back(s);
  }
  return STEPS_OK;
}
```

- [ ] **Step 7: Run the tests**

Run (WSL): `bash /mnt/c/Users/Strad/Desktop/Folder/FlowCE-Steps/tests/host/run_steps_tests.sh`
Expected: the steps of each problem printed, then `6/6 cases pass`. Read the printed expressions too: each one must be mathematically right and readable (e.g. `diff(x^3+5x,x)`: `[Sum rule] :: diff(x^3,x)+5`, `[Power rule] :: 3*x^2+5`). If a label differs, fix `rule()`, not the cases. If the build fails on a giac name (`is_one`, `is_linear_wrt`), look it up in `src/giac/*.h` (`grep -n "bool is_one" src/giac/gen.h`) and use the declared signature.

- [ ] **Step 8: Check the calculator build still links and record its size**

Run: `FLOWCE_WSL_DISTRO=Ubuntu KB=/home/toadvine/flowce-build tools/dev/build.sh en`
Expected: `[build] OK`, size noted (steps.cc is linked only if referenced; at this point it is not yet referenced, so the size may not change: that is fine).

- [ ] **Step 9: Commit**

```bash
git add src/steps.h src/steps.cc tests/host/steps_cases.txt tests/host/check_steps.py tests/host/run_steps_tests.sh tools/hostgiac/khicas_post.cc tools/hostgiac/driver.cc tools/hostgiac/Makefile
git commit -m "Steps: derivative tracer core (sum, constant multiple, power) with host tests (hostgiac -S)"
git push -q origin steps
```

---

### Task 3: All derivative rules

**Files:**
- Modify: `src/steps.cc` (`rule()`)
- Modify: `tests/host/steps_cases.txt`

**Interfaces:**
- Consumes: `rule`, `D`, `mul`, `neg`, `add`, `prod`, `pw`, `txt`, `sym1`, `sym2`, `free_of` from Task 2.
- Produces: no new names; `steps_build` explains every derivative in the cases below.

- [ ] **Step 1: Add the failing cases**

Append to `tests/host/steps_cases.txt`:

```text
diff(x^2*sin(3x),x) :: Product rule, Power rule, Chain rule
diff(sin(x^2),x) :: Chain rule, Power rule
diff(e^x/x,x) :: Quotient rule, Derivative of exp
diff(5/x^2,x) :: Reciprocal rule, Power rule
diff(ln(cos(x)),x) :: Chain rule, Derivative of cos
diff(sqrt(x^2+1),x) :: Chain rule, Sum rule, Power rule
diff(sec(x)*tan(x),x) :: Product rule, Derivative of sec, Derivative of tan
diff(asin(2x),x) :: Chain rule
diff(atan(x^2),x) :: Chain rule, Power rule
diff(2^x*cos(x),x) :: Product rule, Exponential rule, Derivative of cos
diff(x^x,x) :: Logarithmic differentiation, Product rule, Derivative of ln
diff((x^2+1)^5,x) :: Chain rule, Sum rule, Power rule
diff(e^(3x)*ln(x),x) :: Product rule, Chain rule, Derivative of ln
diff(x*e^x*sin(x),x) :: Product rule, Product rule, Derivative of exp, Derivative of sin
diff(cot(x)+csc(x),x) :: Sum rule, Derivative of cot, Derivative of csc
diff(acos(x)-log10(x),x) :: Difference rule, Derivative of acos, Derivative of log10
diff(abs(x^2-4),x) :: Chain rule, Difference rule, Power rule
diff(3x^2,x,2) :: Constant multiple rule, Power rule, Simplify, Differentiate again, Linear function
diff(sin(x),x,3) :: Derivative of sin, Differentiate again, Derivative of cos, Differentiate again, Constant multiple rule, Derivative of sin
diff(t^2*sin(t),t) :: Product rule, Power rule, Derivative of sin
diff(x*x*x*x*x*sin(x),x) :: Product rule
diff(f(x),x) :: NONE
diff(floor(x),x) :: NONE
```

- [ ] **Step 2: Run the tests to see the new cases fail**

Run (WSL): `bash /mnt/c/Users/Strad/Desktop/Folder/FlowCE-Steps/tests/host/run_steps_tests.sh`
Expected: `6/29 cases pass` or close (Task 2's pass; most new ones print `NO STEPS`; the two NONE cases may already pass).

- [ ] **Step 3: Extend `rule()`**

In `src/steps.cc`, replace the `at_prod` block and the `at_pow` block of `rule()`, and add the new blocks before its final `return false;`:

```cpp
  if (s==at_prod){
    vecteur c,f; // the constant factors, the others
    for (unsigned i=0;i<v.size();++i)
      (free_of(v[i],x)?c:f).push_back(v[i]);
    if (f.empty()) return false;
    if (!c.empty()){
      r=mul(prod(c),D(prod(f),x));
      label="Constant multiple rule";
      return true;
    }
    if (f.size()==1) return false;
    const gen g=prod(vecteur(f.begin()+1,f.end())); // f[0] times the rest: (fg)'=f'g+fg'
    r=add(makevecteur(mul(D(f[0],x),g),mul(f[0],D(g,x))));
    label="Product rule";
    choice="f = "+txt(f[0])+", g = "+txt(g);
    return true;
  }
  if (s==at_division){
    const gen & p=v[0], & q=v[1];
    if (free_of(q,x)){
      r=sym2(at_division,D(p,x),q);
      label="Constant multiple rule";
      return true;
    }
    if (free_of(p,x)){ // (c/g)'=-c*g'/g^2
      r=neg(sym2(at_division,mul(p,D(q,x)),sym2(at_pow,q,2)));
      label="Reciprocal rule";
      choice="g = "+txt(q);
      return true;
    }
    r=sym2(at_division,sym2(at_binary_minus,mul(D(p,x),q),mul(p,D(q,x))),sym2(at_pow,q,2));
    label="Quotient rule";
    choice="f = "+txt(p)+", g = "+txt(q);
    return true;
  }
  if (s==at_pow){
    const gen & b=v[0], & e=v[1];
    if (free_of(e,x)){ // (u^n)'=n*u^(n-1)*u'
      const gen m=eval(e-1,1,contextptr);
      if (b==x){
        r=mul(e,pw(x,m));
        label="Power rule";
        return true;
      }
      r=mul(mul(e,pw(b,m)),D(b,x));
      label="Chain rule";
      choice="outer u^"+txt(e)+", inner u = "+txt(b);
      return true;
    }
    if (free_of(b,x)){ // (a^u)'=a^u*ln(a)*u'
      r=mul(mul(u,sym1(at_ln,b)),D(e,x));
      if (e==x) label="Exponential rule";
      else {
        label="Chain rule";
        choice="outer "+txt(b)+"^u, inner u = "+txt(e);
      }
      return true;
    }
    // both depend on x: y=b^e, ln(y)=e*ln(b), y'=y*(e*ln(b))'
    const gen l=mul(e,sym1(at_ln,b));
    r=mul(u,D(l,x));
    label="Logarithmic differentiation";
    choice="ln(y) = "+txt(l);
    return true;
  }
  if (s==at_sqrt){ // (sqrt(u))'=u'/(2*sqrt(u))
    const gen & b=v[0];
    r=sym2(at_division,D(b,x),mul(2,u));
    if (b==x) label="Square root rule";
    else {
      label="Chain rule";
      choice="outer sqrt(u), inner u = "+txt(b);
    }
    return true;
  }
  // f(u) of the table: f'(u)*u'
  const gen & b=v[0];
  gen fp;
  if (s==at_exp) fp=u;
  else if (s==at_ln) fp=sym2(at_division,1,b);
  else if (s==at_log10) fp=sym2(at_division,1,mul(b,sym1(at_ln,10)));
  else if (s==at_sin) fp=sym1(at_cos,b);
  else if (s==at_cos) fp=neg(sym1(at_sin,b));
  else if (s==at_tan) fp=sym2(at_pow,sym1(at_sec,b),2);
  else if (s==at_sec) fp=mul(u,sym1(at_tan,b));
  else if (s==at_csc) fp=neg(mul(u,sym1(at_cot,b)));
  else if (s==at_cot) fp=neg(sym2(at_pow,sym1(at_csc,b),2));
  else if (s==at_asin) fp=sym2(at_division,1,sym1(at_sqrt,sym2(at_binary_minus,1,sym2(at_pow,b,2))));
  else if (s==at_acos) fp=neg(sym2(at_division,1,sym1(at_sqrt,sym2(at_binary_minus,1,sym2(at_pow,b,2)))));
  else if (s==at_atan) fp=sym2(at_division,1,sym2(at_plus,1,sym2(at_pow,b,2)));
  else if (s==at_abs) fp=sym2(at_division,b,u);
  else return false;
  const string name=s.ptr()->s; // "sin"
  r=mul(fp,D(b,x));
  if (b==x) label="Derivative of "+name;
  else {
    label="Chain rule";
    choice="outer "+name+"(u), inner u = "+txt(b);
  }
  return true;
```

Notes for the implementer:
- `s.ptr()->s` is how answer.cc reads a function's name (`g._SYMBptr->sommet.ptr()->s`, answer.cc:39).
- `makevecteur(a,b)` is giac's two-element vector (`src/giac/gen.h`).
- `at_cot`, `at_csc`: check they are declared (`grep -n "at_csc\b\|at_cot\b" src/giac/*.h`); they are used by answer.cc already.
- The expected label for `diff(x*x*x*x*x*sin(x),x)` is only the first one: the parse may already be `x^5*sin(x)`; the case checks the trace finishes (6 factors stay under `STEPS_MAX`) rather than exact steps.

- [ ] **Step 4: Run the tests**

Run (WSL): `bash /mnt/c/Users/Strad/Desktop/Folder/FlowCE-Steps/tests/host/run_steps_tests.sh`
Expected: `29/29 cases pass`. Read every printed trace: the choice lines must name the right parts (`f = x^2, g = sin(3*x)`), and the expressions must be correct mathematics. A case printing `NO STEPS` because `same()` failed on a correct step (a trig identity simplify misses, e.g. `sec(x)^2` against `1+tan(x)^2`): make `same()` also accept `is_zero(simplify(texpand(e-d)))`, re-run, and say so in the commit message.

- [ ] **Step 5: Commit**

```bash
git add src/steps.cc tests/host/steps_cases.txt
git commit -m "Steps: product, quotient, chain, exponential, log, trig and inverse trig rules; logarithmic differentiation; higher derivatives"
git push -q origin steps
```

---

### Task 4: The Steps screen and the 2nd F4 hook

**Files:**
- Create: `src/focus_steps.cc`
- Modify: `src/focus.h` (declarations), `src/focus.cc` (`focus_input_line`, `focus_steps_key`), `src/main.h:103`, `src/main.cc` (after `console_cycle_form`), `src/console.cc:2358-2363` (key), `src/console.cc:3701-3707` (bar label)

**Interfaces:**
- Consumes: `steps_build`, `steps_applicable`, `step`, `STEPS_*` (Task 2).
- Produces:

```cpp
// focus.h
int focus_input_line(int out);  // the input line of the calculation whose result is line out; -1 none
int focus_steps_key();          // 2nd F4 shows steps: the result F4 would cycle comes from a derivative
void focus_steps(const std::string & problem,const std::vector<step> & v,int status,int oom); // the Steps screen
// main.h
void console_show_steps(int in,int out); // 2nd F4: steps of the calculation (in: its input line, out: its result)
```

- [ ] **Step 1: The screen, `src/focus_steps.cc`**

```cpp
// focus_steps.cc - the Steps screen of the Focus interface (2nd F4 on a derivative's result,
// main.cc console_show_steps): the problem, then each step (its rule in bold, what was chosen,
// the expression in 2D), scrolled one step at a time with up and down; clear goes back.
#include <string.h>
#include "console.h"           // maps std to ustl
#include "focus.h"
#include "k_defs.h"
#include "ui_gfx.h"
#include "ui_font.h"
#include "ui_fontdata.h"
#include "ui_math.h"
#include "steps.h"

extern "C" volatile unsigned char focus_phase;
enum { ST = 16, SBOT = 218, MX = 10, MW = 300, EHMAX = 70, MAXLV = 3 };

static unsigned char col(int c) { return ui_col(0, c); }
static const unsigned char * ramp(int fg, int bg) { return ui_ramp(0, fg, bg); }

// one item from y (label, choice, expression; empty parts skipped); returns its height. draw = 0
// measures only.
static int item(const char * label, const char * choice, const char * expr, int y, int draw) {
  int h = 4;
  if (*label) { if (draw) ui_draw_text(&ui_tb10, label, -1, MX, y + h + 10, ramp(UC_ACC, UC_BG), 0); h += 14; }
  if (*choice) { if (draw) ui_draw_text(&ui_tr10, choice, -1, MX, y + h + 10, ramp(UC_SUB, UC_BG), 0); h += 14; }
  mi_layout L;
  int lv = ui_math_fit(expr, strlen(expr), -1, MAXLV, MW, EHMAX, MI_F_IMPLDOT, L);
  if (draw && y + h + L.asc + L.desc <= SBOT) ui_math_draw(L, expr, lv, MX, y + h + L.asc, 0, UC_INK, UC_BG, UC_ACC);
  return h + L.asc + L.desc + 6;
}

// the screen from item top (0: the problem, k: step k-1); returns 1 if items remain below
static int paint(const std::string & problem, const std::vector<step> & v, const char * msg, int top) {
  ui_noclip();
  ui_fill(0, ST, UI_W, SBOT - ST, col(UC_BG));
  ui_clip(0, ST, UI_W, SBOT);
  int y = ST + 2, n = v.size() + 1;
  for (int i = top; i < n; ++i) {
    const char * lab = i ? v[i - 1].label.c_str() : "Problem";
    const char * ch = i ? v[i - 1].choice.c_str() : "";
    const char * ex = i ? v[i - 1].expr.c_str() : problem.c_str();
    int h = item(lab, ch, ex, y, 0);
    if (y + h > SBOT && i > top) { ui_noclip(); return 1; }
    item(lab, ch, ex, y, 1);
    y += h;
    if (i < n - 1) ui_fill(MX, y - 3, MW, 1, col(UC_LINE));
  }
  if (msg) ui_draw_text(&ui_tr12, msg, -1, MX, y + 18, ramp(UC_SUB, UC_BG), 0);
  ui_noclip();
  return 0;
}

void focus_steps(const std::string & problem, const std::vector<step> & v, int status, int oom) {
  static const char * const TABS[5] = {"", "", "", "", "back"};
  const char * msg = status == STEPS_OK ? 0 : status == STEPS_NONE ? "No steps for this one. The answer is still correct."
                     : oom ? "Out of memory" : "Stopped";
  focus_status_label("STEPS");
  focus_bar_tabs(TABS, -1);
  int top = 0, more = 0;
  for (;;) {
    focus_phase = 70;
    more = paint(problem, v, msg, top);
    focus_phase = 0;
    int k;
    GetKey(&k);
    if (k == KEY_CTRL_EXIT || k == KEY_CTRL_AC || k == KEY_CTRL_F5 || k == KEY_CTRL_DEL) break;
    if (k == KEY_CTRL_DOWN && more) ++top;
    if (k == KEY_CTRL_UP && top > 0) --top;
  }
  reset_kbd();
  focus_status_label(0);
  focus_invalidate(); // the console repaints everything
}
```

Notes for the implementer:
- `GetKey`, `reset_kbd`, `focus_status_label`, `focus_bar_tabs`, `focus_invalidate` are used the same way in `focus_catalog.cc` (`focus_catalog()`); copy any include that file needs and this one lacks.
- `UC_BG`, `UC_INK`, `UC_SUB`, `UC_ACC`, `UC_LINE`, `UI_W` come from `ui_gfx.h`; `ui_tb10`, `ui_tr10`, `ui_tr12` from `ui_fontdata.h`.
- `focus_bar_tabs(TABS, -1)`: check how `focus_catalog.cc` passes "no tab on"; if -1 is not accepted, pass the index of an empty label.

- [ ] **Step 2: Find the input line and decide the key in `src/focus.cc`**

After `focus_result_line()` (focus.cc:897-901) add:

```cpp
int steps_applicable(const char * input); // steps.cc
// the input line of the calculation whose result is history line out (-1: none)
int focus_input_line(int out) {
  scan();
  if (!NE || out < 0) return -1;
  int k = entry_of_line(out);
  return k >= 0 && k < NE ? E[k].in : -1;
}
// 2nd F4 shows steps: the result F4 would cycle comes from a derivative
int focus_steps_key() {
  int o = focus_result_line(), i = o >= 0 ? focus_input_line(o) : -1;
  return i >= 0 && steps_applicable((const char *)Line[i].str);
}
```

In `src/focus.h`, after `int focus_result_line();` add the three declarations of this task's Interfaces (`focus_input_line`, `focus_steps_key`, `focus_steps`); `focus_steps` needs `struct step;` declared above it and `<string>`/`<vector>` already mapped by `console.h`: write

```cpp
struct step;
int focus_input_line(int out);  // the input line of the calculation whose result is line out; -1 none
int focus_steps_key();          // 2nd F4 shows steps: the result F4 would cycle comes from a derivative
void focus_steps(const std::string & problem, const std::vector<step> & v, int status, int oom); // focus_steps.cc
```

If `focus.h` is included somewhere `std::string` is not yet declared, move the `focus_steps` declaration into `steps.h` instead (it already includes giac) and include `steps.h` in `main.cc`.

- [ ] **Step 3: Run the trace like the F4 forms, `src/main.cc` and `src/main.h`**

In `src/main.h`, after `void console_cycle_form(int l);` (line 103) add:

```cpp
  void console_show_steps(int in,int out); // 2nd F4 on a derivative's result: its steps (main.cc)
```

In `src/main.cc`, add `#include "steps.h"` with the other local includes, and after the end of `console_cycle_form` (the `}` before `#endif`, main.cc:628) add:

```cpp
// 2nd F4 on a derivative's result: its worked steps (steps.cc) on the Steps screen
// (focus_steps.cc). As for the forms: giac's notes are not shown, ON or a full memory stop it.
void console_show_steps(int in,int out){
  using namespace giac;
  std::string problem;
  std::vector<step> v;
  statuslinemsg("computing...");
  stdostream * savelog=logptr(contextptr);
  logptr(0,contextptr);
  dconsole_mode=0;
  int r=steps_build((const char *)Line[in].str,std::string((const char *)Line[out].str),problem,v);
  logptr(savelog,contextptr);
  dconsole_mode=1;
  const bool oom=oom_hit;
  if (oom || ctrl_c || interrupted){
    ctrl_c=interrupted=false;
    v.clear();
    r=STEPS_STOPPED;
  }
  oom_rearm();
  statuslinemsg("");
  focus_steps(problem,v,r,oom);
}
```

- [ ] **Step 4: Route the key and label it, `src/console.cc`**

After the F4 block (console.cc:2358-2363, ending `continue; }`) add:

```cpp
    // Focus: 2nd F4 on a derivative's result shows its steps (main.cc); elsewhere its menu
    if (focus_on && key==KEY_CTRL_F9 && focus_steps_key()){
      const int o=focus_result_line();
      console_show_steps(focus_input_line(o),o);
      Console_Disp(1);
      continue;
    }
```

In `console_fkey_label` (console.cc:3701), before its last `return`, add:

```cpp
  if (layer==1 && k==3 && focus_on && focus_steps_key()) return "steps";
```

- [ ] **Step 5: Build**

Run: `FLOWCE_WSL_DISTRO=Ubuntu KB=/home/toadvine/flowce-build tools/dev/build.sh en`
Expected: `[build] OK`, `room left:` positive. Record the size; if the build says TOO BIG, stop and report the numbers (spec: next removal needs the user's agreement).

- [ ] **Step 6: Check on the emulator (screenshots)**

WSL script (`KHICAS_ROM`, `KB` exported as in Task 1; `$C` = `tools/emu/cemu.py`):

```bash
export KB=~/flowce-build KHICAS_ROM=~/flowce-build/emu/rom/TI84CE.rom
C=/mnt/c/Users/Strad/Desktop/Folder/FlowCE-Steps/tools/emu/cemu.py
python3 /mnt/c/Users/Strad/Desktop/Folder/FlowCE-Steps/tools/emu/install.py en base $KB/emu/shots
python3 $C base - $KB/emu/shots 'type:diff(x^2*sin(3x),x)' key:enter run:4000 shot:s1_answer key:2nd run:200 shot:s2_bar key:trace run:6000 shot:s3_steps key:down run:500 shot:s4_scrolled key:clear run:800 shot:s5_back
python3 $C base - $KB/emu/shots 'type:factor(x^2-1)' key:enter run:3000 key:2nd key:trace run:1500 shot:s6_notderiv
python3 $C base - $KB/emu/shots 'type:diff(f(x),x)' key:enter run:3000 key:2nd key:trace run:3000 shot:s7_none
```

(F4 is the `trace` key on the CE: the F-keys are the top row y=, window, zoom, trace, graph (cemu key names yequ, window, zoom, trace, graph). If 2nd+F4 does not reach `KEY_CTRL_F9` (s3 shows the polynomial menu), find the code with a `statuslinemsg` of the key value and adjust the `console.cc` test.)

Look at each screenshot (copy them to the scratchpad and Read them):
- s1: the answer; s2: the 2nd bar shows "steps" on F4; s3: Steps screen, "Problem" then "Product rule" with `f = x², g = sin(3x)`, d/dx drawn as a fraction; s4: scrolled by one item; s5: back to the console, intact.
- s6: the polynomial menu (unchanged behaviour). s7: "No steps for this one. The answer is still correct."
- ON: run `'type:diff(x^2*sin(3x)*e^x*ln(x)*cos(x)*tan(x),x)' key:enter run:6000 key:2nd key:trace run:50 key:on run:2000 shot:s8_on key:clear run:500 'type:1+1' key:enter run:1500 shot:s9_after`: s8 shows the steps or "Stopped", s9 shows 2 (the console still works).

- [ ] **Step 7: Commit**

```bash
git add src/focus_steps.cc src/focus.h src/focus.cc src/main.h src/main.cc src/console.cc
git commit -m "Steps screen: 2nd F4 on a derivative's result shows its worked steps

_DEMO.bin <size> B, room <room> B."
git push -q origin steps
```

---

### Task 5: Regression run and a build for her calculator

**Files:**
- Modify: none in src (unless the suite finds a regression)
- Create (outside the repo): `C:\Users\Strad\Desktop\Folder\flowce-build-out\FlowCE.b84`, `_site/` served locally

**Interfaces:**
- Consumes: the build of Task 4 (`$KB/out/en/AppIns*.8xv`), `$KB/emu/arTIfiCE.8xp`, `app_tools/INST.8xp`.

- [ ] **Step 1: Full emulator suite**

As Task 1 Step 5 with output `$KB/results/steps1.txt`. Expected: `SAME` against the baseline DIFF/TIMEOUT/HANG lines.

- [ ] **Step 2: Host steps tests again**

Run (WSL): `bash .../tests/host/run_steps_tests.sh` → `29/29 cases pass`.

- [ ] **Step 3: Bundle `FlowCE.b84`**

The web installer expects the arTIfiCE program named `A` and `INST` plus `AppIns00..`. Check the name inside the arTIfiCE file first: `python3 -c "d=open('$KB/emu/arTIfiCE.8xp','rb').read(); print(d[0x3c:0x44])"` must print `b'A\x00...'`. If it is not `A`, take arTIfiCE from the official release instead: download `https://github.com/tommyb3ll/FlowCE/releases/download/v1.9/FlowCE.b84` (ask the user first: it is a download) and extract with `site/dusb.js`'s `readBundle` logic, or ask the user for the files from their earlier install.

WSL script:

```bash
KB=~/flowce-build; O=/mnt/c/Users/Strad/Desktop/Folder/flowce-build-out; mkdir -p $O
args=""; for f in $(ls $KB/out/en/AppIns*.8xv | sort -V); do args="$args -i $f"; done
$KB/CEdev/bin/convbin -j 8x -k b84 $args -i $KB/emu/arTIfiCE.8xp -i $KB/src/app_tools/INST.8xp -o $O/FlowCE.b84
ls -l $O/FlowCE.b84
```

Expected: `FlowCE.b84` of about 2.8 MB.

- [ ] **Step 4: Serve the install page locally**

Git Bash, repo root:

```bash
site/build.sh ../flowce-build-out/FlowCE.b84 v1.9-steps1
```

Then (WSL, or any Python on Windows) `python3 -m http.server 8000 --directory _site`, and open `http://localhost:8000/` in Chrome: the page must load and show version `v1.9-steps1`. Do not click Install (the user does that with their calculator). `_site/` is in `.gitignore`? Check with `git status`; if not ignored, add `_site/` to `.gitignore` in this commit.

- [ ] **Step 5: Commit and hand over**

```bash
git add .gitignore
git commit -m "Steps part 1: suite clean (715 problems), host steps tests 29/29; local install page"
git push -q origin steps
```

Tell the user: plug in the calculator, open `http://localhost:8000/` in Chrome while the server runs, click Install (it erases the archive, as before), then try `2nd` `F4` on a derivative.
