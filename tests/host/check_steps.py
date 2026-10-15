#!/usr/bin/env python3
"""Checks hostgiac -k -S -p output against tests/host/steps_cases.txt.
Usage: check_steps.py <cases> <output>. Each case: its labels must appear in order among the
problem's [label] lines (a final [Simplify] may follow); '=labels' expects exactly those labels
(a final Simplify or Add the constant aside); ':: NONE' expects '(no steps)'. An
optional third field ('input :: labels :: text') is text that must appear in the problem's
output (math in a choice line is printed between backquotes). '(stopped)' always fails. Exit 1
on any failure."""
import re, sys

cases = []
for line in open(sys.argv[1], encoding='utf-8'):
    line = line.strip()
    if not line or line.startswith('#'):
        continue
    parts = line.split(' :: ')
    exp = parts[1] if len(parts) > 1 else ''
    cases.append((parts[0].strip(), [e.strip() for e in exp.split(',') if e.strip()], parts[2:]))

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
for inp, exp, must in cases:
    b = blocks.get(inp)
    if b is None:
        print('MISSING', inp); bad += 1; continue
    text = '\n'.join(b)
    missing = [m for m in must if m not in text]
    if missing:
        print('TEXT', inp, 'missing', missing, '\n' + text); bad += 1; continue
    if '(stopped)' in text:
        print('STOPPED', inp); bad += 1; continue
    if exp == ['NONE']:
        if '(no steps)' not in text:
            print('EXPECTED NONE', inp, '\n' + text); bad += 1
        continue
    if '(no steps)' in text:
        print('NO STEPS', inp, '\n' + text); bad += 1; continue
    labels = re.findall(r'^  \[([^\]]+)\]', text, re.M)
    if exp and exp[0].startswith('='):  # '=labels': exactly these (the final Simplify/Add the constant aside)
        exp = [exp[0][1:]] + exp[1:]
        got = [l for l in labels if l not in ('Simplify', 'Add the constant')]
        if got != exp:
            print('EXACT', inp, 'expected', exp, 'got', labels); bad += 1
        continue
    i = 0
    for lab in labels:
        if i < len(exp) and lab == exp[i]:
            i += 1
    if i < len(exp):
        print('LABELS', inp, 'expected', exp, 'got', labels); bad += 1
print(f'{len(cases) - bad}/{len(cases)} cases pass')
sys.exit(1 if bad else 0)
