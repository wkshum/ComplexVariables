

# Test whethe four points lie on a circle
def test_concyclic(pt0, pt1, pt2, pt3):
	z0 = complex(pt0[0],pt0[1])   # convert to complex numbers
	z1 = complex(pt1[0],pt1[1])
	z2 = complex(pt2[0],pt2[1])
	z3 = complex(pt3[0],pt3[1])
	return abs(((z0-z1)*(z2-z3)/((z0-z3)*(z2-z1))).imag)< 1e-8
