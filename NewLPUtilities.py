import Matrix_Utils
from fractions import Fraction

def highlightPos(self, tempPos, names = None):
	if names == None:
		content = self.content
		m = self.m
		n = self.n
		pos = [tempPos[0], tempPos[1]]
	else:
		content = list(names)
		if len(content) == self.n - 1:
			content.append('.b')
		else:
			Utils.lenCheck(names, self.content[0], 'variable names', 'collumns')
		content = [content]
		content.extend(self.content)
		m = self.m + 1
		n = self.n
		pos = [tempPos[0] + 1, tempPos[1]]
	stringSize = list(map(lambda j: max(map(lambda i: len(str(content[i][j])), range(m))), range(n)))
	val = '['
	for i in range(m + 2):
		tempI = m
		if i < pos[0]:
			tempI = i
		elif i == pos[0] + 1:
			tempI = i - 1
		elif i > pos[0] + 2:
			tempI = i - 2
		val += '['
		for j in range(n + 2):
			tempJ = n
			if j < pos[1]:
				tempJ = j
			elif j == pos[1] + 1:
				tempJ = j - 1
			elif j > pos[1] + 2:
				tempJ = j - 2
			if tempJ == n:
				if tempI == m:
					val += 'O'
				else:
					val += '|'
			else:
				if tempI == m:
					val += '-' * (stringSize[tempJ] + 2)
				else:
					val += ' '
					elem = str(content[tempI][tempJ])
					val += (' '*(stringSize[tempJ]-len(elem)))
					val += elem
					val += ' '
		val += ']'
		if i != (m + 1):
			val += '\n '
	val += ']'
	print(val)

def DeprecatedGoalLP(constraints, weights = None):
	if weights == None:
		weights = [1]*len(constraints)
	elif type(weights) == type(list()):
		Matrix_Utils.Utils.lenCheck(constraints, weights, 'constraints', 'weights')
	elif type(weights) == type(int()):
		weights = [(lambda j: 1 if j == weights else 0)(i) for i in range(len(constraints))]
	else:
		raise TypeError('The second argument, if provided must be a list or integer.')
	newNames = ['']
	rows = len(constraints)
	for i in range(rows):
		newNames = Matrix_Utils.Utils.unionLists(newNames, constraints[i][1])
	data = [[]] * rows
	b = [[0]] * rows
	revConstr = [False] * rows
	for i in range(rows):
		rowList = Matrix_Utils.EqnUtils.coeffReAlign(constraints[i][0], constraints[i][1], newNames)[0]
		if rowList[0] > 0:
			rowList = list(map(lambda i: -i, rowList))
			revConstr[i] = True
		bEntry = rowList.pop(0)
		data[i] = rowList
		b[i] = [-bEntry]
	A = Matrix_Utils.Matrix(data)
	cols = A.n
	fullMat = A.extendRight(Matrix_Utils.Matrix.identity(rows)).extendRight(Matrix_Utils.Matrix.identity(rows).scalMult(-1))
	LP = fullMat.extendRight(Matrix_Utils.Matrix(b))
	zRow = [1]
	zRow.extend([0] * cols)
	for i in range(rows):
		if (constraints[i][2] == '<' and revConstr[i] == False) or (constraints[i][2] == '>' and revConstr[i] == True):
			zRow.append(0)
		else:
			zRow.append(-weights[i])
	for i in range(rows):
		if (constraints[i][2] == '>' and revConstr[i] == False) or (constraints[i][2] == '<' and revConstr[i] == True):
			zRow.append(0)
		else:
			zRow.append(-weights[i])
	zRow.append(0)
	goalLPTab = Matrix_Utils.Matrix([zRow]).extendBelow(LP)
	return [goalLPTab, LP, list(map(lambda i: 0 if i == 0 else -zRow[i], range(len(zRow))))]

def simplexTab(tempEquations, objVar = None, slackVar = '.s'): #The objective equation should be in the equations entry.
	rows = len(tempEquations)
	equations = [[]] * rows
	newNames = ['']
	if type(objVar) == type(str()):
		if objVar == '':
			raise Exception("'' is reserved for constant values.")
	elif objVar != None:
		raise Exception("The second argument of 'simplexTab' must be a string, if provided.")
	for i in range(rows):
		equations[i] = Matrix_Utils.EqnUtils.eqFromIneq(tempEquations[i], slackVar + str(i))
	for i in range(rows):
		newNames = Matrix_Utils.Utils.unionLists(newNames, equations[i][1])
	if objVar in newNames:
		newNames = Matrix_Utils.Utils.unionLists(['', objVar], newNames)
	data = [Matrix_Utils.EqnUtils.coeffReAlign(equations[i][0], equations[i][1], newNames)[0] for i in range(rows)]
	objRow = list()
	matContent = list()
	constCol = list()
	if objVar in newNames:
		objRows = list(filter(lambda i: i[1] != 0, data))
		if len(objRows) == 1:
			tempRow = data.pop(Matrix_Utils.Utils.firstTrue(data, lambda i: i == objRows[0]))
			objRow = list(map(lambda i: Fraction(i, tempRow[1]), tempRow))
		else:
			tempNames = list(newNames)
			newNames = Matrix_Utils.Utils.unionLists(['','.',objVar], newNames)
			objRow = Matrix_Utils.EqnUtils.coeffReAlign([1,-1],['.',objVar], newNames)[0]
			data = list(map(lambda i: Matrix_Utils.EqnUtils.coeffReAlign(i, tempNames, newNames)[0], data))
		constCol.append(objRow.pop(0))
		matContent.append(objRow)
	for i in range(len(data)):
		bEntry = -data[i].pop(0)
		matRow = list(data[i])
		if bEntry < 0:
			bEntry *= -1
			matRow = list(map(lambda i: -i, matRow))
		#elif bEntry == 0 and all(map(lambda i: i <= 0, matRow)):
		#	matRow = list(map(lambda i: -i, matRow))
		constCol.append(bEntry)
		matContent.append(matRow)
		#print(matContent)
		#input()
	A = Matrix_Utils.Matrix(matContent)
	B = Matrix_Utils.Matrix(list(map(lambda i: [i], constCol)))
	LP = A.extendRight(B)
	return [LP, newNames[1:]]

def appendZRow(zEqn, zName, mat, names):  #Note that 'names' applies to all except the last term in the matrix.
	if zName not in zEqn[1]:
		raise Exception('The objective variable must be in the objective equation.')
	newNames = Matrix_Utils.Utils.unionLists(['', zName], names)

def runGoalLP(constraints, weights = None, **exArgs):  #For preemptive, [[constraint],[constraint],...]; for weights, [[constraint, constraint, constraint]].  Weights should match.
	if 'display' in exArgs:
		display = exArgs['display']
	else:
		display = True
	if 'pause' in exArgs:
		pause = exArgs['pause']
	else:
		pause = display
	additionalConstraints = []  #Used for the preemptive part of the methood.
	constEqs = []  #This is going to take the main constraints, and put them into equations.
	if weights == None:
		weights = [[1] * len(constraints[i]) for i in range(len(constraints))]
	else:
		Matrix_Utils.Utils.lenCheck(constraints, weights, 'constraint groups', 'weight groups')
		for i in range(len(constraints)):
			Matrix_Utils.Utils.lenCheck(constraints[i], weights[i], 'constraints in this block', 'weights in this block')
	for bI in range(len(constraints)):
		for cI in range(len(constraints[bI])):
			constEqs.append(Matrix_Utils.EqnUtils.eqFromIneq(constraints[bI][cI], '.s' + str(bI) + '.' + str(cI), '.d' + str(bI) + '.' + str(cI)))
	bI = 0
	while bI < len(constraints):
		objCoeffs = [1]
		objNames = ['.z']
		for cI in range(len(constraints[bI])):
			objCoeffs.extend([-weights[bI][cI]] * 2)
			objNames.extend(['.d' + str(bI) + '.' + str(cI) + '+', '.d' + str(bI) + '.' + str(cI) + '-'])
		equations = []
		equations.append([objCoeffs, objNames, ''])
		equations.extend(constEqs)
		equations.extend(additionalConstraints)
		if display:
			print('\nThis is the tableau for this part of the goal LP.\n')
		optimal = branchBoundMP(equations, '.z', **exArgs)
		newNames = list(objNames)
		newNames[0] = ''
		newCoeffs = list(objCoeffs)
		newCoeffs[0] = optimal['.z']
		additionalConstraints.append([newCoeffs, newNames, ''])
		#print(additionalConstraints)
		bI += 1
	return [optimal, constEqs, additionalConstraints]

def optimize(mat, min = True, names = None, **exArgs):
	if 'display' in exArgs:
		display = exArgs['display']
	else:
		display = True
	if 'pause' in exArgs:
		pause = exArgs['pause']
	else:
		pause = display
	output = []
	if min:
		output = mat.simplexAlgMin()
	else:
		output = mat.simplexAlgMax()
	if display:
		for i in range(len(output[4])):
			highlightPos(output[3][i], output[4][i], names)
			if pause:
				input()
		output[3][-1].matPrint(names)
		print('\nThe above tableau should be optimal.\n')
		if pause:
			input()
	return output

def pivots(mat, names = None, **exArgs):
	if 'display' in exArgs:
		display = exArgs['display']
	else:
		display = True
	if 'pause' in exArgs:
		pause = exArgs['pause']
	else:
		pause = display
	output = mat.pivBuilder()
	if display: # and output[5]:
		for i in range(len(output[4])):
			highlightPos(output[3][i], output[4][i], names)
			if pause:
				input()
		output[3][-1].matPrint(names)
		print('\nThe above tableau should be valid.\n')
		if pause:
			input()
	return output

def branchBoundMP(tempEquations, objVar, min = True, **exArgs):
	if 'intVars' in exArgs:
		tempIntVars = exArgs['intVars']
	else:
		tempIntVars = []
	if 'binVars' in exArgs:
		binVars = exArgs['binVars']
	else:
		binVars = []
	if 'showSteps' in exArgs:
		showSteps = exArgs['showSteps']
	else:
		showSteps = True
	if 'pauseSteps' in exArgs:
		pauseSteps = exArgs['pauseSteps']
	else:
		pauseSteps = showSteps
	intVars = Matrix_Utils.Utils.unionLists(tempIntVars, binVars)
	eqnList = []#Equations
	valList = []#Optimal Values of each constraint set.
	def addLP(data):
		LP = simplexTab(data, objVar = objVar)
		if showSteps:
			LP[0].matPrint(LP[1])
			print('\nThis is the tableau for this step.\n')
			if pauseSteps:
				input()
		pivoted = pivots(LP[0], LP[1], **exArgs)
		if pivoted[5]:
			optimal = optimize(pivoted[0], min, LP[1], **exArgs)
			values = optimal[0].valListFromSimplex()
			vals = {}
			for i in range(len(LP[1])):
				vals[LP[1][i]] = values[i]
			if showSteps:
				optimal[0].matPrint(LP[1])
				print('\nThis is the optimal tableau for this step.\n\nBelow are the values it corresponds with:\n')
				Matrix_Utils.EqnUtils.printMeaning(vals)
				if pauseSteps:
					input()
			eqnList.append(data)
			valList.append(vals)
		elif showSteps:
			print('There is no solution for this tableau.')
			if pauseSteps:
				input()
	def valid(values):
		keyVals = dict(map(lambda i: (i, values[i]), filter(lambda i: i in intVars, values)))
		return all(map(lambda i: Matrix_Utils.Utils.isInt(keyVals[i]), keyVals))
	if min:
		selector = Matrix_Utils.Utils.minIndex
	else:
		selector = Matrix_Utils.Utils.maxIndex
	equations = list(tempEquations)
	for var in binVars:
		equations.append([[-1,1],['',var], '<'])
	invalid = True
	while invalid:
		addLP(equations)
		if len(valList) == 0:
			raise ValueError('The provided constraints have no integer solutions.')
		idealInd = selector(valList, lambda i: i[objVar])
		idealLP = eqnList.pop(idealInd)
		vals = valList.pop(idealInd)
		if valid(vals):
			invalid = False
		else:
			splitVarInd = Matrix_Utils.Utils.firstTrue(intVars, lambda i: not Matrix_Utils.Utils.isInt(vals[i]) if i in vals else False)
			splitVar = intVars[splitVarInd]
			splitVal = vals[splitVar]
			LowerLP = list(idealLP)
			HigherLP = list(idealLP)
			LowerLP.append([[-(splitVal//1), 1], ['', splitVar], '<'])
			HigherLP.append([[(-splitVal)//1, 1], ['', splitVar], '>'])
			addLP(LowerLP)
			equations = list(HigherLP)
	if showSteps:
		print('\nBelow is the ideal set of values.\n')
		Matrix_Utils.EqnUtils.printMeaning(vals)
		if pauseSteps:
			input()
	return vals


















