"""Exact rational checks for a scoped profile-space baseline obstruction.

These do not prove the actual-zero-measure attachment or simulate (A).
All transcendental comparisons below use only 3 < pi < 22/7.
"""
from fractions import Fraction as Q
from pathlib import Path
import json

d=Q(1,250)
pi_lo,pi_hi=Q(3),Q(22,7)
# c - 4/pi = 4/pi - 48d - 48 pi^2 d^3.
margin=4/pi_hi-48*d-48*pi_hi*pi_hi*d**3
assert margin>0
gap_left,gap_right=Q(401,800),Q(2007,4000)
delta_max=Q(1,4000)
assert Q(501,1000)+delta_max==gap_left
assert gap_right<Q(251,500)
assert gap_right-gap_left==Q(1,2000)
derivative_mass=Q(500)**2*(gap_right-gap_left)
assert derivative_mass==125
assert 4*derivative_mass==500
# The real tent has integral J'^2=1000 and integral J^2=1/750.
tent_d1=2*Q(500)**2*Q(1,500)
tent_l2=2*Q(500)**2*Q(1,500)**3/3
assert tent_d1==1000 and tent_l2==Q(1,750)
target_upper=8/pi_lo*tent_d1+88*pi_hi*tent_l2
# Once actual target norm <= B0(J,J)+1 and actual residual >=250/pi,
# the relative gap is bounded below by this fixed positive rational.
relative_gap_lower=(250/pi_hi)/(target_upper+1)
assert relative_gap_lower>Q(29,1000)
result={
 "status":"PASS",
 "scope":"Coercivity and support constants only; actual attachment remains a separate proof obligation",
 "support_width":str(d),
 "coercivity_margin_above_4_over_pi_lower_bound":str(margin),
 "gap_interval":[str(gap_left),str(gap_right)],
 "delta_max":str(delta_max),
 "gap_derivative_energy":str(derivative_mass),
 "limiting_absolute_gap":"500/pi",
 "eventual_actual_gap_if_attachment_holds":"250/pi",
 "limiting_target_norm":"8000/pi+44*pi/375",
 "eventual_relative_gap_lower_bound_if_attachment_holds":str(relative_gap_lower),
 "relative_gap_exceeds":"29/1000",
 "no_claim_for_arbitrary_bounded_coefficient_sequences":True,
 "no_Lean_certificate":True
}
Path(__file__).with_name('COERCIVITY_CHECKS.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
