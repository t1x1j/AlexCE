// focus_steps.cc - the Steps screen of the Focus interface (2nd F4 on a derivative's result,
// main.cc console_show_steps): the problem, then each step (its rule in bold, what was chosen,
// the expression in 2D), scrolled one step at a time with up and down; clear goes back.
#include <string.h>
#include <time.h>              // (before giac: first.h defines a clock macro)
#include "steps.h"             // giac first, as main.cc: console.h then maps std to ustl
#include "console.h"
#include "menuGUI.h"
#include "focus.h"
#include "k_defs.h"
#include "ui_gfx.h"
#include "ui_font.h"
#include "ui_fontdata.h"
#include "ui_math.h"

extern "C" volatile unsigned char focus_phase;
enum { ST = 16, SBOT = 218, MX = 10, MW = 300, EHMAX = 70, MAXLV = 3, CHOICE_LV = 6 }; // levels: 20 px, 12 px

static unsigned char col(int c) { return ui_col(0, c); }
static const unsigned char * ramp(int fg, int bg) { return ui_ramp(0, fg, bg); }

// a choice line from y: words, and math between \1 marks drawn small in 2D ("outer sin(u), inner
// u = 3x"), on one baseline; returns its height. draw = 0 measures only.
static int choice_line(const char * c, int y, int draw) {
  int asc = 10, desc = 4; // the 10 px text's
  for (int pass = 0; pass <= draw; ++pass) {
    int x = MX, math = 0;
    for (const char * p = c;;) {
      const char * q = strchr(p, '\x01');
      int n = q ? q - p : strlen(p);
      if (n && math) {
        mi_layout L;
        int lv = ui_math_fit(p, n, -1, CHOICE_LV, MW - (x - MX), 40, MI_F_IMPLDOT, L);
        if (!pass) { if (L.asc > asc) asc = L.asc; if (L.desc > desc) desc = L.desc; }
        else ui_math_draw(L, p, lv, x, y + asc, 0, UC_SUB, UC_BG, UC_ACC);
        x += L.width;
      }
      else if (n) {
        if (pass) ui_draw_text(&ui_tr10, p, n, x, y + asc, ramp(UC_SUB, UC_BG), 0);
        x += ui_text_width(&ui_tr10, p, n);
      }
      if (!q) break;
      p = q + 1;
      math = !math;
    }
  }
  return asc + desc + 2;
}

// one item from y (label, choice, expression; empty parts skipped); returns its height. draw = 0
// measures only.
static int item(const char * label, const char * choice, const char * expr, int y, int draw) {
  int h = 4;
  if (*label) { if (draw) ui_draw_text(&ui_tb10, label, -1, MX, y + h + 10, ramp(UC_ACC, UC_BG), 0); h += 14; }
  if (*choice) h += choice_line(choice, y + h, draw);
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
