"""Replay exact certifier and cross-check independent quadrature enclosures."""
import json, subprocess, sys
from pathlib import Path
from fractions import Fraction as F
root=Path(__file__).resolve().parent
p=subprocess.run([sys.executable,str(root/'certify_independent.py')],check=True,capture_output=True,text=True)
(root/'certified.txt').write_text(p.stdout)
c=json.loads((root/'certified.json').read_text());e=json.loads((root/'exploratory.json').read_text())
def contains(iv,s):
 x=F(s);return F(int(iv['lo']),10**55)<=x<=F(int(iv['hi']),10**55)
for den in ['.504','.5']:
 for high,eh in [('printed','printed'),('exact','exact_model')]:
  for tail,et in [('printed','full'),('collapsed','collapsed'),('upstream','upstream_tail')]:
   C=c[f'{den}:{high}:{tail}'];E=e[f'{den}:{eh}:{et}']
   for name in ['c1','c2','c3','c34']:
    for part in ['real','imag']:assert contains(C[name][part],E[name][part]),(den,high,tail,name,part)
   assert contains(C['total'],E['total']['real'])
   assert contains(C['minimum_with_first_coefficient_1'],E['stationary_total']['real'])
   for i in range(4):
    for j in range(4):
     for part in ['real','imag']:assert contains(C['matrix'][i][j][part],E['matrix'][i][j][part]),(den,high,tail,i,j,part)
print('PASS: exact certificate replay and independent 70-digit results agree in all 12 branches')
