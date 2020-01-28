import re
from itertools import takewhile, dropwhile


span = lambda f, xs: (list(takewhile(f, xs)), list(dropwhile(f, xs)))
to_formula = lambda atoms: ''.join([a+(''if atoms[a]==1 else str(atoms[a])) for a in atoms])
apply_coef = lambda coef, atoms: to_formula({atom:atoms[atom]*coef for atom in atoms})


def parse_simple_molecule(formula):
  molecules = re.findall(r'[A-Z][a-z]?\d*', formula)
  l = map(lambda molecule: span(lambda c: c.isalpha(), molecule), molecules)

  atoms = {}
  for (atoml, indexl) in l:
    atom  = ''.join(atoml)
    index = 1 if indexl == [] else int(''.join(indexl))
    if atom in atoms:
      atoms[atom] += index
    else:
      atoms[atom] = index
  
  return atoms


def parse_molecule(formula):
  formula = re.sub(r'\{|\[', '(', formula)
  formula = re.sub(r'\}|\]', ')', formula)

  while '(' in formula:
    for f in re.findall(r'\([^\(]+?\)+\d*', formula):
      if f.endswith(')'):
        formula = formula.replace(f, to_formula(parse_molecule(f[1:-1])))
      else:
        coef = span(lambda c: c.isdigit(), f[::-1])[0][0]
        formula = formula.replace(f, apply_coef(int(coef), parse_molecule(f[1:-len(coef)-1])))

  return parse_simple_molecule(formula)
