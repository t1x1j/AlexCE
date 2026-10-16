// steps.cc - worked steps (steps.h). The typed problem is parsed without being evaluated (giac
// keeps sec, sqrt, a/b as typed), then its unevaluated diff(u,x) nodes are expanded one rule at a
// time, outermost and leftmost first: each expansion is one step. Derivatives a reader sees at
// once (a constant, x, a linear ax+b) are written directly. After each step the expression is
// evaluated and compared with giac's derivative: a step that does not check discards the trace.
#ifndef NO_STEPS // (UNITS=1: units and the steps do not both fit, makefile)
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
// diff(u,x) as diff((u),x), drawn d/dx(u): d/dx x^2 sin(3x) reads as the derivative of the
// product whether it is or not (d/dx(x^2) sin(3x) is not); integrate(a+b,x) as integrate((a+b),x)
// (a sum only), drawn as the integral of (a+b)
static void paren_arg(string & s,const char * fn,bool sum){
  const size_t L=strlen(fn);
  for (size_t p=s.find(fn);p!=string::npos;p=s.find(fn,p+L)){
    const size_t a=p+L;
    size_t i=a;
    int depth=0;
    bool wrapped=s[a]=='(',has=!sum; // already (u): stays wrapped while its parenthesis is open
    for (;i<s.size();++i){
      const char c=s[i];
      if (c=='(') ++depth;
      else if (c==')'){ if (!depth) break; --depth; }
      else if (!depth && c==',') break;
      else if (!depth && i>a){
        wrapped=false;
        if ((c=='+' || c=='-') && !strchr("^*/(e",s[i-1])) has=true;
      }
    }
    if (!wrapped && has && i<s.size() && s[i]==','){
      s.insert(i,")");
      s.insert(a,"(");
    }
  }
}
// a-b as a+(-b): giac prints an unevaluated a-b as (a)-(b)
static gen plain_minus(const gen & g){
  if (g.type!=_SYMB) return g;
  const gen & f=g._SYMBptr->feuille;
  gen n;
  if (f.type==_VECT){
    vecteur v=*f._VECTptr;
    for (unsigned i=0;i<v.size();++i) v[i]=plain_minus(v[i]);
    n=gen(v,f.subtype);
  }
  else n=plain_minus(f);
  if (g._SYMBptr->sommet==at_binary_minus && n.type==_VECT && n._VECTptr->size()==2)
    return sym2(at_plus,n._VECTptr->front(),sym1(at_neg,n._VECTptr->back()));
  return symbolic(g._SYMBptr->sommet,n);
}
// -(diff(u,x)) as -diff(u,x): giac puts a negated call in parentheses
static void unwrap_neg_diff(string & s){
  for (size_t p=s.find("-(diff(");p!=string::npos;p=s.find("-(diff(",p+1)){
    int depth=0;
    size_t i=p+2;
    for (;i<s.size();++i){
      if (s[i]=='(') ++depth;
      else if (s[i]==')' && !--depth) break; // the end of diff(...)
    }
    if (i+1<s.size() && s[i+1]==')'){
      s.erase(i+1,1);
      s.erase(p+1,1);
    }
  }
}
// a negative factor after * or / in parentheses: exp(-x)*(-1), not exp(-x)*-1 (drawn e^-x·−1)
static void paren_neg(string & s){
  for (size_t p=s.find_first_of("*/");p!=string::npos;p=s.find_first_of("*/",p+1)){
    if (p+1>=s.size() || s[p+1]!='-') continue;
    size_t i=p+2;
    int depth=0;
    for (;i<s.size();++i){ // the factor: a number, a name, a call, a power
      const char c=s[i];
      if (c=='(') ++depth;
      else if (c==')'){ if (!depth) break; --depth; }
      else if (!depth && !isalnum((unsigned char)c) && c!='.' && c!='_' && c!='^') break;
    }
    s.insert(i,")");
    s.insert(p+1,"(");
  }
}
// constants put together for reading: a/b/c as a/(b*c), 1/q*(a/b) as a/(q*b) (multiplied out
// when both are numbers)
static gen tmul(const gen & a,const gen & b){ return a.type==_INT_ && b.type==_INT_?a*b:sym2(at_prod,a,b); }
static __attribute__((noinline)) gen tidy(const gen & g){
  if (g.type!=_SYMB) return g;
  const gen & f=g._SYMBptr->feuille;
  gen n;
  if (f.type==_VECT){
    vecteur v=*f._VECTptr;
    for (unsigned i=0;i<v.size();++i) v[i]=tidy(v[i]);
    n=gen(v,f.subtype);
  }
  else n=tidy(f);
  const unary_function_ptr & s=g._SYMBptr->sommet;
  if (n.type==_VECT && n._VECTptr->size()==2){
    const gen a=n._VECTptr->front(),b=n._VECTptr->back();
    if (s==at_division && is_op(a,at_division)) return sym2(at_division,args(a)[0],tmul(args(a)[1],b));
    if (s==at_prod){
      for (int k=0;k<2;++k){
        const gen & c=k?b:a, & d=k?a:b;
        gen q;
        if (c.type==_FRAC && is_one(c._FRACptr->num)) q=c._FRACptr->den;
        else if (is_op(c,at_division) && is_one(args(c)[0]) && args(c)[1].type==_INT_) q=args(c)[1];
        if (!is_zero(q) && is_op(d,at_division)) return sym2(at_division,args(d)[0],tmul(q,args(d)[1]));
      }
    }
  }
  return symbolic(s,n);
}
// g as FlowCE prints answers (the textbook notation of answer.cc)
static __attribute__((noinline)) string txt(const gen & g){
  string s=plain_minus(tidy(g)).print(contextptr);
  textbook(s);
  paren_arg(s,"diff(",false);
  paren_arg(s,"integrate(",true);
  paren_neg(s);
  unwrap_neg_diff(s);
  return s;
}
// math in a choice line, between \1 marks: the Steps screen draws it in 2D
static string m(const string & s){ return "\x01"+s+"\x01"; }
static string m(const gen & g){ return m(txt(g)); }

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
static string uname(const gen & f); // (below)
// a chain rule's choice: outer pre U post, inner U = b (U: u, or w when the variable is u)
static __attribute__((noinline)) string chain(const string & pre,const string & post,const gen & b,const gen & u){
  const string U=uname(u);
  return "outer "+m(pre+U+post)+", inner "+m(U+" = "+txt(b));
}
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
    choice="f = "+m(f[0])+", g = "+m(g);
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
      choice="g = "+m(q);
      return true;
    }
    r=sym2(at_division,sym2(at_binary_minus,mul(D(p,x),q),mul(p,D(q,x))),sym2(at_pow,q,2));
    label="Quotient rule";
    choice="f = "+m(p)+", g = "+m(q);
    return true;
  }
  if (s==at_pow){
    const gen & b=v[0], & e=v[1];
    if (free_of(e,x)){ // (u^n)'=n*u^(n-1)*u'
      const gen e1=eval(e-1,1,contextptr);
      if (b==x){
        r=mul(e,pw(x,e1));
        label="Power rule";
        return true;
      }
      r=mul(mul(e,pw(b,e1)),D(b,x));
      label="Chain rule";
      choice=chain("","^"+txt(e),b,u);
      return true;
    }
    if (free_of(b,x)){ // (a^u)'=a^u*ln(a)*u'
      r=mul(mul(u,sym1(at_ln,b)),D(e,x));
      if (e==x) label="Exponential rule";
      else {
        label="Chain rule";
        choice=chain(txt(b)+"^","",e,u);
      }
      return true;
    }
    // both depend on x: y=b^e, ln(y)=e*ln(b), y'=y*(e*ln(b))'
    const gen l=mul(e,sym1(at_ln,b));
    r=mul(u,D(l,x));
    label="Logarithmic differentiation";
    choice=m("ln(y) = "+txt(l));
    return true;
  }
  if (s==at_sqrt){ // (sqrt(u))'=u'/(2*sqrt(u))
    const gen & b=v[0];
    r=sym2(at_division,D(b,x),mul(2,u));
    if (b==x) label="Square root rule";
    else {
      label="Chain rule";
      choice=chain("sqrt(",")",b,u);
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
  else if (s==at_sinh) fp=sym1(at_cosh,b);
  else if (s==at_cosh) fp=sym1(at_sinh,b);
  else if (s==at_tanh) fp=sym2(at_division,1,sym2(at_pow,sym1(at_cosh,b),2)); // (sech: not a giac function)
  else if (s==at_asinh) fp=sym2(at_division,1,sym1(at_sqrt,sym2(at_plus,sym2(at_pow,b,2),1)));
  else if (s==at_acosh) fp=sym2(at_division,1,sym1(at_sqrt,sym2(at_binary_minus,sym2(at_pow,b,2),1)));
  else if (s==at_atanh) fp=sym2(at_division,1,sym2(at_binary_minus,1,sym2(at_pow,b,2)));
  else if (s==at_abs) fp=sym2(at_division,b,u);
  else return false;
  const string name=s.ptr()->s; // "sin"
  r=mul(fp,D(b,x));
  if (b==x) label="Derivative of "+name;
  else {
    label="Chain rule";
    choice=chain(name+"(",")",b,u);
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
  return !interrupted && (is_zero(ratnormal(d,contextptr),contextptr) || is_zero(simplify(d,contextptr),contextptr)
                          || ((contains(d,at_sinh) || contains(d,at_cosh) || contains(d,at_tanh)) // (no hyperbolic identities)
                              && is_zero(simplify(hyp2exp(d,contextptr),contextptr),contextptr)));
}
// g (its diff nodes evaluated) equals the derivative d
static bool same(const gen & g,const gen & d){ return equal(eval(g,1,contextptr),d); }

// ---------------------------------------------------------------- integrals
// As for derivatives: the problem's unevaluated integrate(f,v) nodes are expanded one rule at a
// time, leftmost first. A step is checked by differentiating it (a node differentiates to its
// integrand): the derivative must be the integrand. A u-substitution traces the integral in u on
// its own, checked in u, before the substitution back (usub).
static gen inode(const gen & f,const gen & v){ return sym2(at_integrate,f,v); }
// a power rule's denominator as written on paper: x^(3/2)/(3/2), x^(-1)/(-1) (giac prints a
// fraction or a negative number below a bar bare: x^(3/2)/3/2)
static gen den(const gen & e){
  if (e.type==_FRAC) return sym2(at_division,e._FRACptr->num,e._FRACptr->den);
  if (is_strictly_positive(-e,contextptr)) return sym1(at_neg,-e);
  return e;
}
// c*g as on paper, c evaluated: g, 3*g, 3*g/4 (not g/1, 1/2*g)
static gen cmul(const gen & c0,const gen & g){
  const gen c=eval(c0,1,contextptr);
  if (c.type==_FRAC) return sym2(at_division,mul(c._FRACptr->num,g),c._FRACptr->den);
  return is_minus_one(c)?neg(g):mul(c,g);
}
// dx, du: the differential of v, for the choice lines
static gen dvar(const gen & v){ return gen("d"+v.print(contextptr),contextptr); }
// E (its integrate nodes unevaluated) is an antiderivative of f in v (derive does not know a
// parsed a-b: plain_minus first; with no node left the derivative can be evaluated)
static bool anti(const gen & E,const gen & f,const gen & v){
  return equal(eval(derive(plain_minus(E),v,contextptr),1,contextptr),eval(f,1,contextptr));
}

// the textbook table, as text (built as trees in code, it took KBs: answer.cc's table0 too): the
// label, the integrand and its antiderivative in x, x then replaced by v. The integrands are
// compared as typed (sec(x)^2), the last two up to their order (1+x^2, x^2+1)
static const char * const TABLE[]={
  "exp","exp(x)","exp(x)", "sin","sin(x)","-cos(x)", "cos","cos(x)","sin(x)",
  "tan","tan(x)","-ln(abs(cos(x)))", "cot","cot(x)","ln(abs(sin(x)))",
  "sec","sec(x)","ln(abs(sec(x)+tan(x)))", "csc","csc(x)","-ln(abs(csc(x)+cot(x)))",
  "sec^2","sec(x)^2","tan(x)", "csc^2","csc(x)^2","-cot(x)",
  "sec*tan","sec(x)*tan(x)","sec(x)", "sec*tan","tan(x)*sec(x)","sec(x)",
  "csc*cot","csc(x)*cot(x)","-csc(x)", "csc*cot","cot(x)*csc(x)","-csc(x)",
  "sec^3","sec(x)^3","(sec(x)*tan(x)+ln(abs(sec(x)+tan(x))))/2",
  "sinh","sinh(x)","cosh(x)", "cosh","cosh(x)","sinh(x)", "tanh","tanh(x)","ln(cosh(x))",
  "sech^2","1/cosh(x)^2","tanh(x)",
  "1/(1+x^2)","1/(1+x^2)","atan(x)", "1/sqrt(1-x^2)","1/sqrt(1-x^2)","asin(x)", 0};
// a of w = a*v+b (w linear in v, not v itself); 0 otherwise
static gen lin_coef(const gen & w,const gen & v){
  if (w==v || free_of(w,v)) return 0;
  const gen a=normal(derive(eval(w,1,contextptr),v,contextptr),contextptr);
  return free_of(a,v)?a:gen(0);
}
// the argument of f's first table function (exp, sin, cos, tan, cot, sec, csc, sinh, cosh, tanh), 0 if none
static gen inner(const gen & f){
  if (f.type!=_SYMB) return 0;
  const unary_function_ptr & s=f._SYMBptr->sommet;
  if (s==at_exp || s==at_sin || s==at_cos || s==at_tan || s==at_cot || s==at_sec || s==at_csc || s==at_sinh || s==at_cosh || s==at_tanh) return f._SYMBptr->feuille;
  const vecteur a=args(f);
  for (unsigned i=0;i<a.size();++i){ const gen w=inner(a[i]); if (!is_zero(w)) return w; }
  return 0;
}
// f in the table, of v or of a linear w = a*v+b (the result over a: cos(3x) gives sin(3x)/3)
static gen free_var(const gen & f); // (below)
// the substitution's name in choice lines: u, or w (t, s) when f uses u
static string uname(const gen & f){ const gen u=free_var(f); return is_zero(u)?string("u"):u.print(contextptr); }
static gen table_int(const gen & f,const gen & v,string & label,string & choice){
  if (f.type!=_SYMB) return 0;
  if (is_op(f,at_pow) && args(f)[1]==v && free_of(args(f)[0],v)){ // a^v/ln(a)
    label="Exponential rule";
    return sym2(at_division,f,sym1(at_ln,args(f)[0]));
  }
  const gen x("x",contextptr),w0=inner(f),a=is_zero(w0)?gen(0):lin_coef(w0,v);
  for (int pass=0;pass<2;++pass){
    if (pass && is_zero(a)) break;
    const gen w=pass?w0:v;
    for (int k=0;TABLE[k];k+=3){
      if (pass && TABLE[k][0]=='1') continue; // (1/(1+x^2), 1/sqrt(1-x^2): the argument v only)
      const gen p=quotesubst(gen(TABLE[k+1],contextptr),x,w,contextptr);
      if (f==p || (TABLE[k][0]=='1' && is_op(f,at_division) && equal(f,p))){
        label=string("Integral of ")+TABLE[k];
        const gen r=quotesubst(gen(TABLE[k+2],contextptr),x,w,contextptr);
        if (!pass) return r;
        choice=m(uname(f)+" = "+txt(w))+": divide by "+m(txt(a));
        return is_one(a)?r:sym2(at_division,r,den(a));
      }
    }
  }
  return 0;
}

static int itrace(gen & E,const gen & f,const gen & v,vector<step> & out); // (below)
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
  // a function itself too: u = ln(x) for ln(x)/x, u = sin(x) for sin(x)cos(x)
  if (a.size()==1 && s!=at_neg && !equalposcomp(c,f)) c.push_back(f);
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
static __attribute__((noinline)) bool usub(const gen & f,const gen & v,gen & r,string & label,string & choice,vector<step> & pre){
  if (usub_depth>=2) return false;
  vecteur c;
  candidates(f,v,c);
  const gen u=free_var(f);
  if (is_zero(u)) return false;
  for (unsigned i=0;i<c.size();++i){
    const gen & b=c[i];
    const gen db=normal(derive(eval(b,1,contextptr),v,contextptr),contextptr);
    if (is_zero(db) || interrupted) continue;
    // b replaced by u before simplifying: what is left of v must cancel (x/(x^2+1) over 2x: 1/(2u));
    // evaluated (normal leaves an unevaluated 2x*cos(u)/(2x) as is), then parsed again from its
    // text (evaluated, 1/u is inv(u): the rules know the typed forms)
    // u = tan(w): sec(w)^2 is 1+u^2 (giac's derivative of tan is 1+tan^2), du shown as sec(w)^2 dx;
    // u = sec(w): du = sec(w)tan(w) dx kept as written (giac's is sin/cos^2: tan would not cancel)
    gen ff=f,dd=db,dshow=db;
    if (is_op(b,at_tan)){
      const gen s2=sym2(at_pow,sym1(at_sec,b._SYMBptr->feuille),2);
      ff=quotesubst(f,s2,sym2(at_plus,1,sym2(at_pow,b,2)),contextptr);
      dshow=cmul(normal(db/(1+b*b),contextptr),s2);
    }
    if (is_op(b,at_sec)){
      const gen w=b._SYMBptr->feuille;
      dd=dshow=cmul(normal(derive(eval(w,1,contextptr),v,contextptr),contextptr),sym2(at_prod,b,sym1(at_tan,w)));
    }
    const gen G0=normal(eval(quotesubst(sym2(at_division,ff,dd),b,u,contextptr),1,contextptr),contextptr);
    if (!free_of(G0,v) || interrupted) continue;
    const gen G(G0.print(contextptr),contextptr);
    const size_t n0=pre.size();
    step s={"u-substitution","Let "+m(txt(u)+" = "+txt(b))+", "+m(txt(dvar(u))+" = "+txt(mul(dshow,dvar(v)))),txt(inode(G,u))};
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
static __attribute__((noinline)) bool parts(const gen & f,const gen & v,gen & r,string & label,string & choice){
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
  string tl,tc; // v from the table first (sinh(x) for cosh(x): giac answers in exponentials)
  gen V=table_int(dV,v,tl,tc);
  if (is_zero(V)) V=normal(_integrate(makesequence(eval(dV,1,contextptr),v),contextptr),contextptr);
  if (interrupted || is_undef(V) || V.type==_STRNG || contains(V,at_integrate)) return false;
  const gen dU=normal(derive(eval(U,1,contextptr),v,contextptr),contextptr),d=dvar(v);
  // the new integral as text: a long one is no textbook step (and parts again on it grows without
  // end until giac cannot read it back)
  const string vdu=normal(mul(V,dU),contextptr).print(contextptr);
  if (vdu.size()>200) return false;
  ++parts_count;
  r=sym2(at_plus,mul(U,V),neg(inode(gen(vdu,contextptr),v)));
  label="Integration by parts";
  choice=m("u = "+txt(U))+", "+m("dv = "+txt(mul(dV,d)))+"\n"+m("du = "+txt(mul(dU,d)))+", "+m("v = "+txt(V));
  return true;
}
// the integral of f appearing again in E (by parts twice: e^x sin x): E = A + k*I, so I = A/(1-k)
static __attribute__((noinline)) bool again(gen & E,const gen & f,const gen & v,string & label,string & choice){
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
  // I = A - I/4, so I = (A)/(5/4): k*I written as on paper (-I, -I/4, 2*I)
  const gen I=identificateur("I"),c2=eval(-k,1,contextptr);
  const gen kI=!is_strictly_positive(c2,contextptr)?mul(k,I):
    neg(c2.type==_FRAC?sym2(at_division,mul(c2._FRACptr->num,I),c2._FRACptr->den):mul(c2,I));
  choice=m("I = "+txt(sym2(at_plus,A,kI)))+"\nso "+m("I = "+txt(sym2(at_division,A,den(eval(1-k,1,contextptr)))));
  return true;
}

static gen deg_v(const gen & p,const gen & v){ return _degree(makesequence(p,v),contextptr); }
// f evaluated, a rational function of v alone (no other variable or function); 0 otherwise
static gen rat_v(const gen & f,const gen & v){
  const gen e=eval(f,1,contextptr);
  const vecteur l=lvar(e);
  return l.size()==1 && l.front()==v?e:gen(0);
}
// a rational function of v: division first when not proper (Polynomial division), else the
// decomposition (Partial fractions); one term left (an irreducible quadratic below) goes to split_num
static __attribute__((noinline)) bool pfrac(const gen & f,const gen & v,gen & r,string & label,string & choice){
  const gen e=rat_v(f,v);
  if (is_zero(e)) return false;
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
  const gen P=tidy(gen(_partfrac(makesequence(e,v),contextptr).print(contextptr),contextptr));
  if (!is_op(P,at_plus) && !is_op(P,at_binary_minus)) return false;
  r=inode(P,v);
  label="Partial fractions";
  choice=m(txt(f)+" = "+txt(P));
  return true;
}
// (Bx+C)/Q, Q quadratic: k*Q'/Q + C2/Q (k = B over Q's x coefficient), the first a ln|Q| by a
// u-substitution, the second an arctangent; C/Q alone: Q's square completed
static __attribute__((noinline)) bool split_num(const gen & f,const gen & v,gen & r,string & label,string & choice){
  const gen e=rat_v(f,v);
  if (is_zero(e)) return false;
  const gen N=_numer(e,contextptr),Q=_denom(e,contextptr);
  const gen dq=deg_v(Q,v),dn=deg_v(N,v);
  if (dq.type!=_INT_ || dq.val!=2 || dn.type!=_INT_ || dn.val>1) return false;
  const gen dQ=normal(derive(Q,v,contextptr),contextptr);
  if (dn.val==0){
    // a*((x+h)^2+k): the leading coefficient out first
    const gen a=_coeff(makesequence(Q,v,2),contextptr),S0=gen(_canonical_form(makesequence(normal(Q/a,contextptr),v),contextptr).print(contextptr),contextptr);
    const gen S=is_one(a)?S0:mul(a,S0);
    if (S==Q) return false;
    r=inode(sym2(at_division,N,S),v);
    label="Complete the square";
    choice=m(txt(Q)+" = "+txt(S));
    return true;
  }
  const gen k=normal(_coeff(makesequence(N,v,1),contextptr)/_coeff(makesequence(dQ,v,1),contextptr),contextptr);
  const gen C2=normal(N-k*dQ,contextptr),I1=mul(k,inode(sym2(at_division,dQ,Q),v));
  r=is_zero(C2)?I1:sym2(at_plus,I1,inode(sym2(at_division,C2,Q),v));
  label="Split the numerator";
  const bool mi=is_strictly_positive(-C2,contextptr);
  choice=m(txt(N)+" = "+(is_one(k)?string("("):txt(k)+"*(")+txt(dQ)+")"+(is_zero(C2)?string():(mi?" - ":" + ")+txt(mi?-C2:C2)));
  return true;
}

// trig substitution for sqrt(a^2-x^2) (x = a sin t), sqrt(x^2+a^2) (x = a tan t), sqrt(x^2-a^2)
// (x = a sec t): the integral in t traced on its own (pre), then back-substituted by the triangle
static __attribute__((noinline)) bool trig_sub(const gen & f,const gen & v,gen & r,string & label,string & choice,vector<step> & pre){
  if (usub_depth>=2) return false;
  const vecteur roots=lop(f,at_sqrt);
  if (roots.size()!=1) return false;
  const gen R=eval(roots[0]._SYMBptr->feuille,1,contextptr),v2=v*v;
  const gen k=normal(R-v2,contextptr),k2=normal(R+v2,contextptr); // R = v^2+k, or R = k2-v^2
  int kind;
  gen a2;
  if (free_of(k2,v) && is_strictly_positive(k2,contextptr)){ kind=0; a2=k2; }       // a^2-x^2
  else if (free_of(k,v) && is_strictly_positive(k,contextptr)){ kind=1; a2=k; }     // x^2+a^2
  else if (free_of(k,v) && is_strictly_positive(-k,contextptr)){ kind=2; a2=-k; }   // x^2-a^2
  else return false;
  gen t("t",contextptr);
  if (contains(f,t) || !(eval(t,1,contextptr)==t)) t=free_var(f);
  if (is_zero(t)) return false;
  const gen a=eval(sym1(at_sqrt,a2),1,contextptr),ga("a",contextptr),gt("t",contextptr),gx("x",contextptr);
  // x = a sin t, a tan t, a sec t; dx; the root as a cos t, a sec t, a tan t (t in the usual range);
  // back: sin t, cos t, tan t and t by the triangle
  static const char * const T[]={"a*sin(t)","a*cos(t)","a*cos(t)","x/a","sqrt(a^2-x^2)/a","x/sqrt(a^2-x^2)","asin(x/a)",
                                 "a*tan(t)","a*sec(t)^2","a*sec(t)","x/sqrt(x^2+a^2)","a/sqrt(x^2+a^2)","x/a","atan(x/a)",
                                 "a*sec(t)","a*sec(t)*tan(t)","a*tan(t)","sqrt(x^2-a^2)/x","a/x","sqrt(x^2-a^2)/a","atan(sqrt(x^2-a^2)/a)"};
  gen g[7];
  for (int i=0;i<7;++i){
    const char * tp=T[7*kind+i];
    if (i<3 && is_one(a)) tp+=2; // ("a*sin(t)": sin(t))
    g[i]=quotesubst(quotesubst(quotesubst(gen(tp,contextptr),ga,a,contextptr),gt,t,contextptr),gx,v,contextptr);
    if (i>2) g[i]=gen(eval(g[i],1,contextptr).print(contextptr),contextptr); // (sqrt(9-x^2), not sqrt(3^2-x^2))
  }
  const gen G0=normal(eval(quotesubst(quotesubst(f,roots[0],g[2],contextptr),v,g[0],contextptr)*g[1],1,contextptr),contextptr);
  if (!free_of(G0,v) || interrupted) return false;
  // the integral in t as it comes (2*tan(t)^2), else in sin and cos (cos(t)/(4*sin(t)^2))
  const size_t n0=pre.size();
  gen Et;
  for (int pass=0;;++pass){
    if (pass>1 || interrupted) return false;
    gen G((pass?normal(_tan2sincos(G0,contextptr),contextptr):G0).print(contextptr),contextptr);
    if (!pass && is_op(G,at_division)){ // c/cos(t)^n (sec(t) evaluated) as the table has it: c*sec(t)^n
      const gen q=args(G)[1],c=is_op(q,at_pow)?args(q)[0]:q,n=is_op(q,at_pow)?args(q)[1]:gen(1);
      if (is_op(c,at_cos) && n.type==_INT_ && free_of(args(G)[0],t)) G=mul(args(G)[0],pw(sym1(at_sec,c._SYMBptr->feuille),n));
    }
    step s={"Trig substitution",m(txt(v)+" = "+txt(g[0]))+", "+m(txt(dvar(v))+" = "+txt(mul(g[1],dvar(t))))+"\n"+m(txt(roots[0])+" = "+txt(g[2])),txt(inode(G,t))};
    pre.push_back(s);
    Et=inode(G,t);
    ++usub_depth;
    const int kk=itrace(Et,G,t,pre);
    --usub_depth;
    if (kk==STEPS_OK) break;
    pre.resize(n0);
  }
  // sin 2t = 2 sin t cos t first (texpand), sec, csc, cot by cos and sin, then the triangle, then t
  const gen S=sym1(at_sin,t),C=sym1(at_cos,t);
  gen F=_texpand(eval(Et,1,contextptr),contextptr);
  // abs(g) set aside first (substituted, giac writes it sqrt(g^2) when it cannot tell the sign): F and
  // each g substituted together, each g simplified alone, then put back in an abs
  const vecteur ab=lop(F,at_abs);
  vecteur all(1,F),ph;
  if (ab.size()<10){
    for (unsigned i=0;i<ab.size();++i){
      ph.push_back(gen(string("steps_A")+char('0'+i),contextptr));
      all.push_back(ab[i]._SYMBptr->feuille);
    }
    all[0]=subst(F,ab,ph,false,contextptr);
  }
  gen V(all);
  V=subst(V,makevecteur(sym1(at_sec,t),sym1(at_csc,t),sym1(at_cot,t)),makevecteur(inv(C,contextptr),inv(S,contextptr),C/S),false,contextptr);
  V=subst(V,makevecteur(S,C,sym1(at_tan,t)),makevecteur(g[3],g[4],g[5]),false,contextptr);
  V=subst(V,t,g[6],false,contextptr);
  if (V.type!=_VECT || V._VECTptr->size()!=all.size()) return false;
  const vecteur & w=*V._VECTptr;
  F=normal(eval(w[0],1,contextptr),contextptr);
  for (unsigned i=0;i<ph.size();++i) F=quotesubst(F,ph[i],sym1(at_abs,normal(eval(w[i+1],1,contextptr),contextptr)),contextptr);
  // the root as typed (sqrt(9-x^2), not sqrt(-x^2+9))
  string fs=F.print(contextptr);
  const string from="sqrt("+normal(R,contextptr).print(contextptr)+")",to=roots[0].print(contextptr);
  for (size_t q=fs.find(from);q!=string::npos;q=fs.find(from,q+to.size())) fs.replace(q,from.size(),to);
  r=gen(fs,contextptr);
  label="Back-substitute";
  choice=m(txt(S)+" = "+txt(g[3]))+", "+m(txt(C)+" = "+txt(g[4]))+"\n"+m(txt(t)+" = "+txt(g[6]));
  return true;
}
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
// trig integrals: an odd power (3 or more) keeps one factor and turns the rest by
// sin^2 + cos^2 = 1 (then a u-substitution); even powers of both: the power-reducing identities
// (tlin); tan^n (n >= 2): tan^(n-2)*(sec^2 - 1)
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
  if ((M%2 && M>=3) || (N%2 && N>=3)){ // keep one factor of the odd power (sin first: u = cos)
    const bool s=M%2 && M>=3;
    const gen keep=s?S:C,other=s?C:S;
    const int o=(s?M:N)-1;
    const gen id=sym2(at_binary_minus,1,sym2(at_pow,other,2)); // 1 - cos^2 (or 1 - sin^2)
    r=inode(mul(mul(c,pw(id,o/2)),mul(pw(other,s?N:M),keep)),v);
    label="Pythagorean identity";
    choice=m(txt(sym2(at_pow,keep,2))+" = "+txt(id));
    return true;
  }
  if (M%2 || N%2) return false; // sin*cos^n, sin^n*cos: a u-substitution
  r=inode(gen(_tlin(eval(f,1,contextptr),contextptr).print(contextptr),contextptr),v);
  label="Power-reducing identity";
  const gen c2=sym1(at_cos,eval(2*w,1,contextptr));
  choice=M?m(txt(sym2(at_pow,S,2))+" = "+txt(sym2(at_division,sym2(at_binary_minus,1,c2),2))):string();
  if (N) choice+=(M?", ":"")+m(txt(sym2(at_pow,C,2))+" = "+txt(sym2(at_division,sym2(at_plus,1,c2),2)));
  return true;
}

// one rule applied to the integral of f in v: its result r (with integrate nodes left for the
// rest), the rule's name, what was chosen, and steps to show before this one (pre: a
// u-substitution's integral in u); false: no rule
static __attribute__((noinline)) bool irule(const gen & f,const gen & v,gen & r,string & label,string & choice,vector<step> & pre){
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
    if (free_of(p,v)){
      // c/(ax+b), c/(ax+b)^n: ln|ax+b|/a, (ax+b)^(1-n)/((1-n)a)
      gen base=q,nb=1;
      if (is_op(q,at_pow) && free_of(args(q)[1],v)){ base=args(q)[0]; nb=args(q)[1]; }
      const gen c=lin_coef(base,v);
      if (!is_zero(c)){
        choice=m(uname(f)+" = "+txt(base));
        if (is_one(nb)){ r=cmul(p/c,sym1(at_ln,sym1(at_abs,base))); label="Log rule"; return true; }
        const gen e=eval(1-nb,1,contextptr);
        r=sym2(at_division,cmul(p/c,pw(base,e)),den(e));
        label="Power rule";
        return true;
      }
      // c/(w^2+k), k > 0, w linear: atan(w/sqrt(k))/(a*sqrt(k))
      if (is_op(q,at_plus) && args(q).size()==2){
        const vecteur t=args(q);
        for (int i=0;i<2;++i){
          const gen & sq=t[i], & k=t[1-i];
          if (!is_op(sq,at_pow) || !(args(sq)[1]==2) || !free_of(k,v) || !is_strictly_positive(k,contextptr)) continue;
          const gen w=args(sq)[0],c2=w==v?gen(1):lin_coef(w,v);
          if (is_zero(c2) || (w==v && is_one(k) && is_one(p))) continue; // (1/(1+x^2): the table)
          const gen sk=normal(eval(sym1(at_sqrt,k),1,contextptr),contextptr),c=normal(eval(p/(c2*sk),1,contextptr),contextptr),at=sym1(at_atan,is_one(sk)?w:sym2(at_division,w,sk));
          r=cmul(c,at);
          label="Integral of 1/(u^2+a^2)";
          choice=m("a = "+txt(sk));
          return true;
        }
      }
      // c/v, c/v^n, c/sqrt(v)
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
    r=sym2(at_division,pw(v,e1),den(e1));
    label="Power rule";
    return true;
  }
  if (s==at_pow && free_of(a[1],v)){ // (ax+b)^n: (ax+b)^(n+1)/((n+1)a)
    const gen c=lin_coef(a[0],v),e1=eval(a[1]+1,1,contextptr);
    if (!is_zero(c) && !is_zero(e1)){
      r=sym2(at_division,pw(a[0],e1),den(eval(e1*c,1,contextptr)));
      label="Power rule";
      choice=m(uname(f)+" = "+txt(a[0]));
      return true;
    }
  }
  if (s==at_sqrt && a[0]==v){
    r=sym2(at_division,sym2(at_pow,v,fraction(3,2)),den(fraction(3,2)));
    label="Power rule";
    choice=m(txt(f)+" = "+txt(v)+"^(1/2)"); // (printed, v^(1/2) is sqrt(v) again)
    return true;
  }
  // a product or integer power of sums that is a polynomial of degree 4 at most: expanded, then
  // term by term (higher, (x^2+1)^5*x: a u-substitution)
  if ((s==at_prod || (s==at_pow && a[1].type==_INT_ && a[1].val>=2)) && (contains(f,at_plus) || contains(f,at_binary_minus)) && poly_v(f,v)){
    const gen d=_degree(makesequence(eval(f,1,contextptr),v),contextptr);
    if (d.type==_INT_ && d.val<=4){
    r=inode(gen(normal(eval(f,1,contextptr),contextptr).print(contextptr),contextptr),v);
    label="Expand";
    return true;
    }
  }
  r=table_int(f,v,label,choice);
  if (!is_zero(r) || trig_rewrite(f,v,r,label,choice)) return true;
  return usub(f,v,r,label,choice,pre) || trig_sub(f,v,r,label,choice,pre) || pfrac(f,v,r,label,choice) || split_num(f,v,r,label,choice) || parts(f,v,r,label,choice);
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
static __attribute__((noinline)) int itrace(gen & E,const gen & f,const gen & v,vector<step> & out){
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
    string l2,c2;
    if (again(E,f,v,l2,c2)){
      if (!anti(E,f,v)) return interrupted?STEPS_STOPPED:STEPS_NONE;
      step t={l2,c2,txt(E)};
      out.push_back(t);
    }
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
    // the traced form when it keeps a sinh, cosh or tanh the answer wrote in exponentials (x sinh x - cosh x)
    const bool hyp=(contains(F,at_sinh) || contains(F,at_cosh) || contains(F,at_tanh)) && !contains(A,at_sinh) && !contains(A,at_cosh) && !contains(A,at_tanh);
    step s={hyp || out.empty() || out.back().expr!=answer?(hyp?"Add the constant":"Simplify"):"Add the constant","",(hyp?out.back().expr:answer)+"+C"};
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

int steps_applicable(const char * s){
  while (*s==' ') ++s;
  return !strncmp(s,"diff(",5) || !strncmp(s,"integrate(",10);
}

int steps_build(const char * input,const string & answer,string & problem,vector<step> & out){
  out.clear();
  usub_depth=parts_count=0;
  problem.clear();
  const int S=strlen(input),cap=2*S+32>256?2*S+32:256;
  char * buf=(char *)malloc(cap);
  if (!buf) return STEPS_STOPPED;
  strcpy(buf,input);
  answer_prepass(buf,cap,true); // as do_run: 2x is 2*x, Focus's log is log10
  const gen in(buf,contextptr);
  free(buf);
  if (is_op(in,at_integrate)){
    const vecteur a=args(in);
    if (a.size()<2 || a[1].type!=_IDNT) return STEPS_NONE;
    const vecteur ids=lidnt(a[0]);
    for (unsigned i=0;i<ids.size();++i)
      if (ids[i]!=a[1] && contains(eval(ids[i],1,contextptr),a[1])) return STEPS_NONE;
    return build_integral(in,answer,problem,out);
  }
  if (!is_op(in,at_diff)) return STEPS_NONE;
  const vecteur a=args(in);
  if (a.size()<2 || a.size()>3 || a[1].type!=_IDNT) return STEPS_NONE;
  const gen x=a[1];
  const int n=a.size()==3?(a[2].type==_INT_?a[2].val:0):1;
  if (n<1 || n>3) return STEPS_NONE;
  problem=txt(in);
  gen f=a[0],last; // last: the derivative found, evaluated (the answer must equal it)
  // a stored variable whose value has x in it (y:=3x+1, then diff(y,x)): the steps would show y
  // and treat it as a constant
  const vecteur ids=lidnt(f);
  for (unsigned i=0;i<ids.size();++i)
    if (ids[i]!=x && contains(eval(ids[i],1,contextptr),x)) return STEPS_NONE;
  for (int k=1;k<=n;++k){
    if (k>1){
      step s={"Differentiate again",k==2?"the second derivative":"the third derivative",txt(dnode(f,x))};
      out.push_back(s);
    }
    const gen d=derive(eval(f,1,contextptr),x,contextptr); // giac's derivative: each step must equal it
    gen g=D(f,x);
    if (!is_op(g,at_diff)){ // a constant or linear function: one step, checked as the others
      if (!same(g,d)){ out.clear(); return interrupted?STEPS_STOPPED:STEPS_NONE; }
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
    // no diff left: the derivative (normal keeps sin, cos; factor keeps (x+1)^2), parsed again from
    // its text, unevaluated as the input: evaluated, a/b is a*inv(b), which no rule differentiates
    last=normal(eval(g,1,contextptr),contextptr);
    f=gen(factor(last,false,contextptr).print(contextptr),contextptr);
    if (k<n){
      step s={"Simplify","",txt(f)};
      out.push_back(s);
    }
  }
  // the last step is the answer as FlowCE shows it, which must be what the steps found
  const gen A=eval(gen(answer,contextptr),1,contextptr);
  if (interrupted){ out.clear(); return STEPS_STOPPED; }
  if (!equal(last,A)){ out.clear(); return interrupted?STEPS_STOPPED:STEPS_NONE; } // (f: parsed, its a-b unevaluated)
  if (out.empty() || out.back().expr!=answer){
    step s={"Simplify","",answer};
    out.push_back(s);
  }
  return STEPS_OK;
}
#endif // NO_STEPS
