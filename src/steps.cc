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

// a equals b: ratnormal first (simplify alone rewrites sin(3x) in tan(3x/2), then the difference
// in tan(3x/4), and never finds 0)
static bool equal(const gen & a,const gen & b){
  const gen d=a-b;
  return !interrupted && (is_zero(ratnormal(d,contextptr),contextptr) || is_zero(simplify(d,contextptr),contextptr));
}
// g (its diff nodes evaluated) equals the derivative d
static bool same(const gen & g,const gen & d){ return equal(eval(g,1,contextptr),d); }

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
    f=normal(eval(g,1,contextptr),contextptr); // no diff left: the derivative (normal keeps sin, cos)
    if (k<n){
      step s={"Simplify","",txt(f)};
      out.push_back(s);
    }
  }
  // the last step is the answer as FlowCE shows it, which must be what the steps found
  const gen A=eval(gen(answer,contextptr),1,contextptr);
  if (interrupted){ out.clear(); return STEPS_STOPPED; }
  if (!equal(f,A)){ out.clear(); return interrupted?STEPS_STOPPED:STEPS_NONE; }
  if (out.empty() || out.back().expr!=answer){
    step s={"Simplify","",answer};
    out.push_back(s);
  }
  return STEPS_OK;
}
