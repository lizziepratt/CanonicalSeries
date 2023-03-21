# Canonical Series Computation
# For 2 variables only

import sage

###################### USAGE ##############################
# Open sage shell
# Navigate to folder
# sage CanonComp.sage


################# Setting up the ring  #################
n = 2
R = PolynomialRing(QQ, [f"p{i}" for i in range(n)])
gens = R.gens()


################## Recurrence class ##############################
# Represents the recurrence f(p)x_p = sum_i hs[i](p)*x_{p-shift[i]}
class Recurrence():
  def __init__(self, f, hs, shifts):
    self.f = f
    self.hs = hs
    self.shifts = shifts

  # List of nodes you need to know to apply recurrence
  def prereqNodes(self, p):
    return [tuple([p[i] - shift[i] for i in range(len(p))]) for shift in self.shifts]

  # Substitute p into self.f, determine if it's singular at that p
  def is_nonsingular(self, p):
    Phi = R.hom(p, QQ)  
    fp = self.f.apply_morphism(Phi)
    return fp.is_invertible()

  def solve_with(self, p, values_so_far_dict):
    Phi = R.hom(p, QQ) 
    hps = [h.apply_morphism(Phi) for h in self.hs]
    fp = self.f.apply_morphism(Phi)
    rhs_terms = [hps[i]*values_so_far_dict[tuple([p[j] - self.shifts[i][j] for j in range(len(p))])] for i in range(len(hps))]
    rhs = sum(rhs_terms) 
    return fp.solve_right(rhs)

#######################################################################
########################### COMMANDS ##################################
#######################################################################

    
### INPUT: ###
# Dimensions n and rk, which give the dimensions of the matrix
# A polynomial f in k[theta]
# A starting monomial stPowerOfX
### OUTPUT: ###
# An (n*rk) x (n*rk) matrix which gives the map f: L_p \to L_p
### Algorithm: ###
# apply the ring homomorphism phi: k[theta] to End L_p
# by replacing each occurence of p_i with 
# Compute phi(f) by computing phi(theta_i), the elementary matrices

def difMatrix(rk, n, f, stPowerOfX, A=[0]*n):
    Mats = MatrixSpace(R, rk**n)
    images = [Mats(elementaryDifMatrix(rk, n, i, A)) for i in range(n)]
    phi = R.hom(images, Mats)
    return shiftMonomialSpace(phi(f), stPowerOfX)

### INPUT: ###
# Dimensions n and rk, which give the dimensions of the matrix
# A number i from 0 to n-1
# A starting monomial A
### OUTPUT: ###
# An (n^rk) x (n^rk) matrix which gives the map \theta_i: L_p \to L_p
### Notes: ###
# To get symbolic matrices, replace the ring R above with 'p'
# and instead of P[ind] write gens[ind]

def elementaryDifMatrix(rk, n, ind=0, A=[0]*n):
    dim = rk^n
    m = matrix(R, dim, dim, lambda i, j: kronecker_delta(i,j)*(A[ind]+gens[ind]))
    
    # Apply the differential operator to x_0^a_0...x_{n-1}^a_{n-1}, 
    # where col = a_0 + a_1r + ... + a_{n-1}r^{n-1} (r-ary notation)
    for col in range(0,dim):
        rkary= Integer(col).digits(rk)
        if len(rkary) > ind and rkary[ind] != 0:
            
            # Apply the derivative to your monomial
            # eg if rkary = [2, 1] then coefficient after applying theta_1 is 2
            coefficient = rkary[ind]  
            rkary[ind] = max(0, rkary[ind]-1)
            row = naryToInt(rkary, rk)
            m[row,col] = coefficient
    return m

### INPUT: ###
# A vector nums of length k + 1
### OUTPUT: ###
# The integer nums[0] + nums[1]*base + ... + nums[k]*base^k
### NOTES: ###
# this algorithm is arcane magic known as lambda calculus
# Reduce is a "left fold". 
# It iterates function over list, using output as the next input
# *base left shifts

def naryToInt(nums, base):
    import functools
    return functools.reduce(lambda x,y: x + y*base, nums)

### INPUT: ###
# A matrix M and an amount to shift by
### OUTPUT: ### 
# The matrix with the ring homomorphism y -> y + shift
def shiftMonomialSpace(M, shift):
    g = list(R.gens())
    for i in range(len(shift)):
        g[i] = g[i]+shift[i]
    Phi = R.hom(g, R)
    return M.apply_morphism(Phi)

### INPUT: ###
# A vector coeffs of length rk^n and vectors P, stPowerOfX of length n
### OUTPUT: ###
# The element of L_P corresponding to this vector
# Formatted in string form
### Example: ###
## The inputs coeffs=[7, 2], P=[3], stPowerOfX=[4] would turn into x^[4](7x^[3] + 2x^[3]log(x))

def vectToSeries(coeffVector, P, stPowerOfX, rk):
    exponent = [P[i] + stPowerOfX[i] for i in range(len(P))]
    term = ""
    
    # Loop over index = power of log
    # Record rkary(index) = [a_1, ..., a_n], i.e. index in base rk
    # Add coeffs[index] x^exponent log(x_1)^a_1 ... log(x_n)^a_n 
    firstTerm = True
    for index in range(len(coeffVector)):
        if coeffVector[index] != 0:
            rkary= Integer(index).digits(rk, padto=2)

            if index == 0:
                term += ("%s" % coeffVector[index])
                firstTerm = False
            else:
                if not firstTerm:
                    term+= " + "
                term += ("%slog(y)^%s" % (coeffVector[index], rkary))
                firstTerm = False
            
    if not (max(coeffVector) == 0 and min(coeffVector) == 0): # Check that the coeffVector is not 0
        term = ("(" + term + ")" +"y^%s" % exponent + " + ")
    return term

### INPUT: ###
# A vector coeffs of length rk^n and vectors P, stPowerOfX of length n
### OUTPUT: ###
# The element of L_P corresponding to this vector
# Formatted in TeX form
### Example: ###
## The inputs coeffs=[7, 2], P=[3], stPowerOfX=[4] would turn into x^4(7x^3 + 2x^3\log(x))
def vectToSeriesTex(coeffVector, P, stPowerOfX, rk):
    exponent = [P[i] + stPowerOfX[i] for i in range(len(P))]
    term = ""
    firstTerm = True
    for index in range(len(coeffVector)):
        if coeffVector[index] != 0:
            rkary= Integer(index).digits(rk, padto=2)

            if index == 0:
                term += ("%s" % coeffVector[index])
                firstTerm = False
            else:
                if not firstTerm:
                    term+= " + "
                term += ("%slog(y_2)^{%s}log(y_3)^{%s}" % (coeffVector[index], rkary[0], rkary[1]))
                firstTerm = False
            
    if not (max(coeffVector) == 0 and min(coeffVector) == 0): # Check that the coeffVector is not 0
        term = ("(" + term + ")" +"y_2^{%s}y_3^{%s}" % (exponent[0], exponent[1]) + " + ")

    # Manually replacing things for TeX formatting
    term = term.replace("log(y_2)^{0}", "")
    term =term.replace("log(y_3)^{0}", "")
    term =term.replace("y_2^{0}y_3^{0}", "1")
    term =term.replace("y_2^{0}", "")
    term =term.replace("y_3^{0}", "")
    term =term.replace("^{1}","")
    term =term.replace("1y_2", "y_3")
    term = term.replace("1log", "log") 
    term = term.replace("log", "\log")
    term = term.replace("(1)", "")

    return term

### INPUT: ### 
# homParts, inhomParts are lists of matrices of size rk^n, 
# homParts contains the matrices of f_i's and inhomParts contains the matrices of h_i's
# shift, stPowerOfX are vectors of length n
# shift tells you to more from space L_p to L_{p + shift} after applying Mh
# startingMonomial is a vector of length rk^n
# k is how many terms of the partial solution to visit
# diagnosticsOn prints extra diagnostics -- use when debugging or to see intermediate steps
### OUTPUT: ### 
# prints the kth partial solution, in string form

def partialSolution(recurrences, stPowerOfX, startingMon, rk, k=5, diagnosticsOn = True):
    
    # Initializing / setup
    startingMonomial = transpose(matrix(startingMon))
    nodes = sum([[tuple(shift) for shift in rec.shifts] for rec in recurrences],  []) # node in the lattice at the origin (tuple) + shifts
    print(nodes)
    coeffs = {
        (0,0):startingMonomial
    }

    
    for i in range(k):
        currentP = nodes.pop(0)

        # Test to see which recurrences you can apply until currentP has a value
        i = 0
        while currentP not in coeffs and i < len(recurrences):
            # DIAGNOSTICS
            if diagnosticsOn:
                print("---------------")
                print("The number of nodes visited is %s" % i)
                print("current P: %s" % str(currentP)) 

            currentRec = recurrences[i]
            prereqs = currentRec.prereqNodes(currentP)  
            prereqsMet = all([prereq in coeffs for prereq in prereqs])          
            if prereqsMet and currentRec.is_nonsingular(currentP):
                # Compute the node
                coeff = currentRec.solve_with(currentP, coeffs)
                coeffs[currentP] = coeff
                if diagnosticsOn: print(f"Just computed the node {currentP}!")

                # Add children
                for rec in recurrences:
                    shifts = rec.shifts
                    for shift in shifts:
                        newP = tuple([currentP[i] + shift[i] for i in range(len(shift))]) 
                        if newP[0]==1 and newP[1]==-1:
                            print("WE CAUGHT ONE BOIZ")
                        if newP not in coeffs:
                            nodes.append(newP)

            elif not currentRec.is_nonsingular(currentP) and diagnosticsOn:
                print("Recurrence %s is singular at node %s" % (currentRec.shifts, currentP))

            elif not prereqsMet and diagnosticsOn:
                print("The prereqs for recurrence %s are not met at nodes %s" % (currentRec.shifts, currentP))

            i+=1
        if i >= len(recurrences):
            nodes.append(currentP)
            if diagnosticsOn: print(f"The node {currentP} could not be computed.")

    return coeffs

### INPUT: ### 
# The coeffs dictionary, starting power of x, rank of system
# Weight vector wVect
### OUTPUT: ### 
# The coeffs dictionary but in string form
# Puts coefficients up to weight N in string form
def coeffsToString(coeffs, stPowerOfX, rk, wVect, N, TeX = False):
    series = ""
    for node in coeffs:
        if wVect[0]*node[0] + wVect[1]*node[1] <= N: 
            if TeX:
                series += str(vectToSeriesTex(coeffs[node].columns()[0], node, stPowerOfX, rk))
            else:
                series += str(vectToSeries(coeffs[node].columns()[0], node, stPowerOfX, rk))
        
    series += "..."
    series = series.replace("+ -", "-")
    return series
  

######################################################################
################################ TESTS ###############################
######################################################################

def Cone1(): # Our case :)
    n = 2
    rk = 4
    stMon1 = [0]*16 # This is the part of the starting monomial that lives in L_0, i.e. log(x)^B in the starting monomial
    stMon1[0] = 1 
    stMon2 = [0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
    stMon3 = [0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0]
    stMon4 = [0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0] 
    stPowerOfX = [0, 0] # This is the A in the SST algorithm (happens to be the same for all starting monomials)
    k = 100
    wVect = [0, 0] # change
    th2 = gens[0]
    th3 = gens[1]
    
    # Element g_1 of the Grobner basis
    shift1 = [1, 0]
    F1 = difMatrix(rk, n,  th2^2, stPowerOfX)
    H1 = shiftMonomialSpace(difMatrix(rk, n, (th2 + th3 + 1)^2, stPowerOfX), [-1, 0])
    rec1 = Recurrence(F1, [H1], [shift1])
    
    # Element g_2 of the Grobner basis
    shift2 = [0, 1]
    F2 = difMatrix(rk, n, th3^2, stPowerOfX)
    H2 = shiftMonomialSpace(difMatrix(rk, n, (th2 + th3 + 1)^2, stPowerOfX), [0, -1])
    rec2 = Recurrence(F2, [H2], [shift2])

    # Partial solution 
    sol = partialSolution([rec1, rec2], stPowerOfX, stMon4, 2, k, diagnosticsOn=False)
    solution = coeffsToString(sol, stPowerOfX, rk, wVect, 10, TeX = True)
    return solution

# Printing matrices to file
def fileTest():   
    sol = Cone1()
    print("The series expansion is:\n")
    print(sol)
    myFile = open("seriesCone1Newhom4", 'w') 
    myFile.write(sol) 
    myFile.close()
    print("done! check your file :)")
#fileTest()

# Test for Recurrences object
def rectest():
    n = 2
    rk = 4
    k = 8
    # Starting monomial
    stMon1 = [1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
    stPowerOfX = [0, 1]

    # Operator
    shifts = ([1,-1], [0,-1])
    F = difMatrix(rk, n, 2*gens[0]*gens[1] + 2*gens[0] + 2*gens[1]^2 + 2*gens[1] + 1, stPowerOfX)
    H1 = shiftMonomialSpace(difMatrix(rk, n, -gens[1]^2-gens[1], stPowerOfX), [-1,1])
    H2 = shiftMonomialSpace(difMatrix(rk, n, gens[1]^2 + gens[1], stPowerOfX), [0,1])
    hs = [H1, H2]
    myRec = Recurrence(F, hs, shifts)
    print("I finished initializing the recurrence")
    print(myRec.prereqNodes([1,-1]))
    print(myRec.is_singular([1, -1]))

# Test for two-variable case
# Operators are dx_2^2 + 1, dx_1 - 1
# Solutions are e^x_1sin(x_2), e^x_1c0s(x_2)
# L_P is spanned by x^p, x^plog(x_1), x^plog(x_2), x^plog(x_1)log(x_2)
def test2():
    n = 2
    rk = 2
    k = 10

    # Solution x_1cos(x_2)
    stMon1 = matrix([1,0,0,0])
    stPowerOfX1 = [0, 0] # a in Bernd's algo

    # Solution x_1sin(x_2)
    stMon2 = matrix([1,0,0,0]) # log(x_1)
    stPowerOfX2 = [0, 1]

    ### Operators ###
    # dx1 - 1 turns into th1 - x1
    shift1 = [1,0]
    F1 = difMatrix(rk, n, gens[0], stPowerOfX1)
    H1 = shiftMonomialSpace(difMatrix(rk, n, 1, stPowerOfX1), [-1,0])
    rec1 = Recurrence(F1, [H1], [shift1])

    # dx2^2 + 1 turns into th2(th2 - 1) + x2^2
    shift2 = [0,2]
    F2 = difMatrix(rk, n, gens[1]*(gens[1]-1),stPowerOfX1)
    H2 = shiftMonomialSpace(difMatrix(rk, n, -1, stPowerOfX1), [0, -2])
    rec2 = Recurrence(F2, [H2], [shift2])

    # Partial solution 
    sol = partialSolution([rec1, rec2], stPowerOfX1, stMon1, 2, k, diagnosticsOn=False)
    solution = coeffsToString(sol, stPowerOfX1, rk, [0,0], 10, TeX = False)
    print("The series expansion up to k = %s is:\n" % k)
    print(solution)
    print("ran")

test2()







