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
