"""Statement-correspondence check for Erdos1088.

Every block between `-- BEGIN VERBATIM <file>` and `-- END VERBATIM` in our Lean files must occur
as a contiguous run of lines in the upstream file `upstream/<file>` (obtained with
`git show c77fdd446d23539302aa73bcfae4a9fa962b8382:<path>` from formal-conjectures), after
removing upstream lines that are pure metadata attributes (`@[category ...]`).
Blank lines are compared too. Exit code 0 iff all blocks match.
"""
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
OURS = [ROOT / 'E1088' / 'Statement' / 'Erdos1088.lean', ROOT / 'E1088' / 'Final.lean']
UP = {'Euclidean.lean': 'Euclidean.lean', 'Metric.lean': 'Metric.lean',
      '1088.lean': '1088.lean'}
UP_ALIAS = {'erdos_1088': '1088.lean'}


def upstream_lines(name):
    lines = (ROOT / 'upstream' / name).read_text(encoding='utf8').splitlines()
    return [l for l in lines if not l.startswith('@[category')]


def contains(hay, needle):
    n = len(needle)
    return any(hay[i:i + n] == needle for i in range(len(hay) - n + 1))


ok = True
nblocks = 0
for f in OURS:
    text = f.read_text(encoding='utf8').splitlines()
    i = 0
    while i < len(text):
        m = re.match(r'-- BEGIN VERBATIM (\S+)', text[i])
        if m:
            key = m.group(1)
            name = UP.get(key) or UP_ALIAS.get(key)
            j = i + 1
            while not text[j].startswith('-- END VERBATIM'):
                j += 1
            block = text[i + 1:j]
            # drop leading/trailing blank lines of the block
            while block and block[0].strip() == '':
                block = block[1:]
            while block and block[-1].strip() == '':
                block = block[:-1]
            up = upstream_lines(name)
            # split block into runs separated by blank lines; each run must be contiguous upstream
            # and the runs must appear in order
            runs, cur = [], []
            for l in block:
                if l.strip() == '':
                    if cur:
                        runs.append(cur)
                    cur = []
                else:
                    cur.append(l)
            if cur:
                runs.append(cur)
            pos = 0
            for run in runs:
                found = -1
                for k in range(pos, len(up) - len(run) + 1):
                    if up[k:k + len(run)] == run:
                        found = k
                        break
                nblocks += 1
                if found < 0:
                    ok = False
                    print(f'MISMATCH in {f.name} block {key}: run starting {run[0]!r}')
                else:
                    pos = found + len(run)
            i = j
        i += 1

# the theorem statement itself must be present
main = (ROOT / 'E1088' / 'Final.lean').read_text(encoding='utf8')
stmt = ('theorem erdos_1088 :\n    ∀ n ≥ 3,\n      (fun d : ℕ ↦ Real.logb 2 (f d n : ℝ)) =o[atTop] '
        '(fun d : ℕ ↦ (d : ℝ)) := by')
if stmt not in main or stmt not in (ROOT / 'upstream' / '1088.lean').read_text(encoding='utf8'):
    ok = False
    print('MISMATCH: erdos_1088 statement text')

print(f'checked {nblocks} verbatim runs: ' + ('ALL MATCH' if ok else 'FAILURES'))
sys.exit(0 if ok else 1)
