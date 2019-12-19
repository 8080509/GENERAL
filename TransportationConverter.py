import Lib
import Matrix_Utils

#Transportation Tab form:
#
#[[costs],[caps],[dems]]
#
#Equivalent to:
#
#[[.......] [[cap1]
# [.costs.]  [capI]
# [.......]] [capM]]
#
# [demands]

def transTabConv(data, isBalanced = False, objVar = '.Z', commonVar = '.x', other = None):  #Takes a Transportation Tableau, and converts it into a cost function and a series of constraints.
	m = len(data[0])
	n = len(data[0][0])
	constrs = []
	objEq = [[1],[objVar],'']
	for i in range(m):
		if data[1][i] != None:
			constrEq = [[-data[1][i]],[''],'<']
			if isBalanced:
				constrEq[2] = ''
			for j in range(n):
				if data[0][i][j] != None:
					constrEq[0].append(1)
					constrEq[1].append(commonVar + str(i) + '.' + str(j))
			constrs.append(constrEq)
	for j in range(n):
		if data[2][j] != None:
			constrEq = [[-data[2][j]],[''],'>']
			if isBalanced:
				constrEq[2] = ''
			for i in range(m):
				if data[0][i][j] != None:
					constrEq[0].append(1)
					constrEq[1].append(commonVar + str(i) + '.' + str(j))
			constrs.append(constrEq)
	for i in range(m):
		for j in range(n):
			if data[0][i][j] != None:
				objEq[0].append(-data[0][i][j])
				objEq[1].append(commonVar + str(i) + '.' + str(j))
	exArgs = dict()
	if other != None:
		vals = list()
		for i in range(m):
			for j in range(n):
				vals.append(commonVar + str(i) + '.' + str(j))
		if other == 'bin':
			exArgs['binVars'] = vals
		elif other == 'int':
			exArgs['intVars'] = vals
	return [objEq, constrs, objVar, exArgs]





























