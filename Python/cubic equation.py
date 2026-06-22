"""
Solving cubic equation using discrete Fourier transform

The default coefficients in the polynomial is 3, 2, 5 and 3, i.e., 
we compute th roots of the polynomial 3*x^3 + 2*x^2 + 5*x+3.

This method use the Lagrange resolvent, which is implemented by
fast Fourier transform fft in the numpy library

The print out of this program is:

The roots of the polynomial with coeff. [3, 2, 5, 3] are
(-0.6122405939418958+0j)
(-0.027213036362385423-1.277734035794487j)
(-0.027213036362385423+1.277734035794487j)
 
Check that they are indeed the roots of the polynomials
The following should be all equal to zero
Value at (-0.6122405939418958+0j) = (-4.440892098500626e-16+0j)
Value at (-0.027213036362385423-1.277734035794487j) = -9.159339953157541e-16j
Value at (-0.027213036362385423+1.277734035794487j) = 9.159339953157541e-16j
"""

from numpy import fft

# evaluate polynomial by Horner's method
def polynomial_evaluate(coef, w):
    z = 0
    for k in range(len(coef)):
        z = (z*w)+coef[k]
    return z

def solve_cubic(coef):
    ''' Solve equation coef[0]*x^3+coef[1]*x^2+coef[2]*x + coef[3] = 0
    '''
    A,B,C,D = coef    # unpack the coefficients
    if A==0:
        print("Degree is not 3")
        return [0]
   
    b = B/A   # normalize by the leading coefficient
    c = C/A
    d = D/A + 2*b**3/27 - c*b/3
    c -= b*b/3
 
    if d==0 and c==0:
        y1=y2=0
    elif c==0:
        y1 = (-d)**(1/3)
        y2 = 0
    else:    
        y1 = ((-d + (d*d+4*c**3/27)**(1/2))/2)**(1/3)
        y2 = -c/(3*y1)
    return list(fft.fft([-b/3,y1,y2]))



coefficients = [3,2,5,3]
roots = solve_cubic(coefficients)
print(f"The roots of the polynomial with coeff. {coefficients} are")
for z in roots:
    print(z)

print(' ')
print('Check that they are indeed the roots of the polynomials')
print('The following should be all equal to zero')
for z in roots:
    print(f"Value at {z} = {polynomial_evaluate(coefficients,z)}")
