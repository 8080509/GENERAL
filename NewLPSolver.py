import Lib
import NewLPUtilities
import Matrix_Utils
eq = Matrix_Utils.EqnUtils.dataFromEqn

equations = [eq(input(' |\n |Input objective equation:  '))]
objVar = input(' |\n |Input objective variable:  ')
minStr = input(' |\n |Do you want to maximize or minimize:  ')
maximize = True
if minStr.lower().startswith('min'):
	maximize = False
print(' |\n |Input Constraints:  ')
looping = True
while looping:
	tempInput = input(' |\n |  ')
	if tempInput:
		equations.append(eq(tempInput))
	else:
		looping = False
print(' |Input Integer Variables:')
intVars = []
looping = True
while looping:
	tempInput = input(' |\n |  ')
	if tempInput:
		intVars.append(tempInput)
	else:
		looping = False
print(' |Input Binary Variables:')
binVars = []
looping = True
while looping:
	tempInput = input(' |\n |  ')
	if tempInput:
		binVars.append(tempInput)
	else:
		looping = False
showSteps = input(' |Do you want the steps of solving each LP shown?\n |\n |  ')
if showSteps.lower().startswith('y'):
	display = True
else:
	display = False
print(' |\n/\n')
NewLPUtilities.branchBoundMP(equations, objVar, not maximize, intVars = intVars, binVars = binVars, display = display)
input()