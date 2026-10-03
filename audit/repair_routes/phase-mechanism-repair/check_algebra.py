from fractions import Fraction as F
from math import comb
import json

checks={}
checks['tau_square_le_d4'] = all((j+1)**2 <= comb(j+3,3) and comb(j+3,3)-(j+1)**2 == j*(j-1)*(j+1)//6 for j in range(1000))
checks['d8_squarefree_local_ratio_le_8'] = all(F(comb(v+8,7),comb(v+7,7)) == F(v+8,v+1) <= 8 for v in range(1000))
checks['ramified_log_exponent']=12+4*9
checks['bare_support_exponent']=str((F(503,1000)+F(499,1000)-1)/2)
checks['kms_bracket_exponent']=str(-F(3,16)*F(1002,1000)+F(11,64))
checks['kms_root_pair_total_exponent']=str(F(1,1000)-F(3,16)*F(1002,1000)+F(11,64))
checks['mqw_allmod_middle_exponent']=str(-F(3,25)*F(499,1000)-F(3,10)*F(503,1000)+F(1,5))
checks['central_A_L2_exponent']=-2022+9*25
checks['central_other_L2_exponent']=-9
checks['central_other_L1_exponent']=str(F(-9,2))
checks['source_prime_plus_count_loss']=-2011+77
checks['prime_plus_square_target_requires_K_less_than']=2011-77-16
# Exact phase ratio uses tau(chi)^2=(-1)^c D.
# Raw i^(b-a)Gamma_a/Gamma_b, relative to tau(chi) D^(s-1),
# acquires (-1)^c. Coefficients below multiply 1,tan,cot respectively.
phases=[]
for c in (0,1):
  for a in (0,1):
    b=(a+c)%2
    factor=(-1)**c * (1j)**(b-a)
    gamma='1' if a==b else ('tan' if a==0 else 'cot')
    phases.append({'chi_parity':c,'psi_parity':a,'factor_real':factor.real,'factor_imag':factor.imag,'gamma_ratio':gamma})
checks['parity_factors']=phases
checks['dilation_norm_exponent']=-1
assert checks['tau_square_le_d4'] and checks['d8_squarefree_local_ratio_le_8']
assert checks['kms_root_pair_total_exponent']=='-3/200'
print(json.dumps(checks,indent=2))
