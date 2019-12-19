from fractions import Fraction

class Matrix:
	def __init__(self, input):
		if type(input) == type(self):
			newInput = input.content
		else:
			newInput = input
		data = list(map(lambda i: list(map(Fraction, i)), newInput))
		good = True
		c = len(data[0])
		for row in data:
			if len(row) != c:
				good = False
		if good:
			self.m = len(data)
			self.n = c
			self.content = data
		else:
			raise IndexError('Rows have different lengths.')
	
	def matAdd(self, mat):
		if (self.m == mat.m and self.n == mat.n):
			return Matrix.matFromCell(lambda i,j: self.content[i][j] + mat.content[i][j], self.m, self.n)
		else:
			print ('Sizes not same')
	
	def matMult(self, mat):
		if (self.n == mat.m):
			return Matrix.matFromCell(lambda i,j: sum([self.content[i][k]*mat.content[k][j] for k in range(self.n)]), self.m, mat.n)
		else:
			print ('Inner indices not same')
	
	def matInnerProd(self, mat):
		if self.n == mat.n and self.m == mat.n:
			acc = 0
			for i in range(self.m):
				for j in range(self.n):
					acc += self.content[i][j]*mat.content[i][j]
			return acc
		else:
			raise IndexError('Sizes not same')
	
	def scalMult(self, scal):
		return Matrix.matFromCell(lambda i,j: self.content[i][j]*scal, self.m, self.n)
	
	def det(self):
		if self.m == self.n:
			if self.n == 1:
				return self.content[0][0]
			else:
				return sum([((-1)**(k))*self.content[0][k]*(Matrix.matFromCell(lambda i,j: self.content[i+1][j+Utils.boolNum(j >= k)], self.m - 1, self.n - 1).det()) for k in range(self.n)])
		else:
			raise IndexError('To compute determinant, matrix must be square.')
	
	def identity(n):
		return Matrix.matFromCell(Utils.kDel, n, n)
	
	def matFromCell(cellEq, r, c):
		return Matrix([[cellEq(i,j) for j in range(c)] for i in range(r)])
	
	def transpose(self):
		return Matrix.matFromCell(lambda i, j: self.content[j][i], self.n, self.m)
	
	def inREF(self):
		REF = True
		RREF = True
		j = 0
		for i in range(self.m):
			if REF:
				k = Utils.pivIndex(self.content[i])
				if k != len(self.content[i]):
					if k <= j:
						REF = False
						RREF = False
					if RREF == True:
						if self.content[i][k] != 1:
							RREF = False
						for l in range(i):
							if self.content[l][k] != 0:
								RREF = False
		return [REF, RREF]
	
	def gJRedux(self, toRREF = False):
		mat = Matrix(self.content)
		fac = Matrix.identity(mat.m)
		inv = Matrix.identity(self.m)
		if not mat.inREF()[0]:
			for i in range(mat.m):
				pivs = list(map(Utils.pivIndex, mat.content))
				for k in range(i):
					pivs[k] = mat.n
				j = min(pivs)
				if j != mat.n:
					k = Utils.firstTrue(pivs, lambda i: i == j)
					E1 = Matrix.matFromCell(lambda r,c: Utils.kDel(r,c) - (Utils.kDel(r,i)*Utils.kDel(i,c) + Utils.kDel(r,k)*Utils.kDel(k,c)) + (Utils.kDel(r,i)*Utils.kDel(k,c) + Utils.kDel(r,k)*Utils.kDel(i,c)), inv.n, mat.m)
					mat = E1.matMult(mat)
					inv = E1.matMult(inv)
					fac = fac.matMult(E1)
					collumn = list(map(lambda row: row[j], mat.content))
					for k in range(i):
						collumn[k] = 0
					mat = Matrix.matFromCell(lambda r,c: Utils.kDel(r,c) - (Utils.kDel(c,i)*collumn[r]*(1-Utils.kDel(r,c))/collumn[i]), mat.m, mat.m).matMult(mat)
					inv = Matrix.matFromCell(lambda r,c: Utils.kDel(r,c) - (Utils.kDel(c,i)*collumn[r]*(1-Utils.kDel(r,c))/collumn[i]), inv.m, inv.m).matMult(inv)
					fac = fac.matMult(Matrix.matFromCell(lambda r,c: Utils.kDel(r,c) + (Utils.kDel(c,i)*collumn[r]*(1-Utils.kDel(r,c))/collumn[i]), fac.n, fac.n))
		if (not mat.inREF()[1]) and toRREF:
			pivs = list(map(Utils.pivIndex, mat.content))
			def func1(i,j):
				if i == mat.n:
					return 1
				else:
					return j[i]
			L1 = list(map(func1, pivs, mat.content))
			mat = Matrix.matFromCell(lambda i,j: Utils.kDel(i,j)/L1[i], mat.m, mat.m).matMult(mat)
			inv = Matrix.matFromCell(lambda i,j: Utils.kDel(i,j)/L1[i], inv.m, inv.m).matMult(inv)
			fac = fac.matMult(Matrix.matFromCell(lambda i,j: Utils.kDel(i,j)*L1[i], fac.n, fac.n))
			for i in range(mat.m):
				if pivs[i] != mat.n:
					data = mat.content
					mat = Matrix.matFromCell(lambda r,c: Utils.kDel(r,c) - (Utils.kDel(c,i)*data[r][pivs[i]]*(1-Utils.kDel(r,c))), mat.m, mat.m).matMult(mat)
					inv = Matrix.matFromCell(lambda r,c: Utils.kDel(r,c) - (Utils.kDel(c,i)*data[r][pivs[i]]*(1-Utils.kDel(r,c))), inv.m, inv.m).matMult(inv)
					fac = fac.matMult(Matrix.matFromCell(lambda r,c: Utils.kDel(r,c) + (Utils.kDel(c,i)*data[r][pivs[i]]*(1-Utils.kDel(r,c))), fac.n, fac.n))
		return [mat, fac, inv]
	
	def makePiv(self, i, j):
		data = self.content
		E1 = Matrix.matFromCell(lambda r,c: Utils.kDel(r,c) - (1 - 1/data[i][j])*Utils.kDel(r,i)*Utils.kDel(i,c), self.m, self.m)
		E2 = Matrix.matFromCell(lambda r,c: Utils.kDel(r,c) - (1 - data[i][j])*Utils.kDel(r,i)*Utils.kDel(i,c), self.m, self.m)
		E3 = Matrix.matFromCell(lambda r,c: Utils.kDel(r,c) - (Utils.kDel(c,i)*data[r][j]*(1-Utils.kDel(r,c))), self.m, self.m)
		E4 = Matrix.matFromCell(lambda r,c: Utils.kDel(r,c) + (Utils.kDel(c,i)*data[r][j]*(1-Utils.kDel(r,c))), self.m, self.m)
		return [E3.matMult(E1), E2.matMult(E4)]
	
	def matPrint(self, names = None):
		if names == None:
			content = self.content
			m = self.m
			n = self.n
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
		stringSize = list(map(lambda j: max(map(lambda i: len(str(content[i][j])), range(m))), range(n)))
		val = '['
		for i in range(m):
			val += '['
			for j in range(n):
				elem = str(content[i][j])
				val += (' '*(stringSize[j]-len(elem)))
				val += elem
				if j != n - 1:
					val += ', '
			val += ']'
			if i != (m - 1):
				val += '\n '
		val += ']'
		print(val)
	
	def selectPivMax(self):
		entVarPos = Utils.minIndex(self.content[0][1:-1], lambda i: i) + 1
		row = self.selectPiv(entVarPos)
		return [row, entVarPos]
	
	def selectPivMin(self):
		entVarPos = Utils.maxIndex(self.content[0][1:-1], lambda i: i) + 1
		row = self.selectPiv(entVarPos)
		return [row, entVarPos]
	
	def selectPiv(self, entVarPos):
		def measure(i, defVal):
			if (i[entVarPos] <= 0) or (i[0] != 0):
				return defVal
			else:
				return i[self.n - 1]/i[entVarPos]
		val = measure(max(self.content, key = lambda i: measure(i, 0)), 0)
		#print(val)
		row = Utils.minIndex(self.content, lambda i: measure(i, 2*val + 1))
		if measure(self.content[row], 2*val + 1) == 2*val + 1:
			row = False
		return row
	
	def rowSelPiv(self, row):
		def valid(col):
			pivInd = self.selectPiv(col)
			if (pivInd != False) and (self.content[row][col] != 0):
				return self.calcPivVal([row, col]) == self.calcPivVal([pivInd, col])
			else:
				return False
		entVarPos = Utils.firstTrue(range(1, self.n - 1), valid) + 1
		if entVarPos == self.n - 1:
			entVarPos = False
		return entVarPos
	
	def simplexAlgMax(self):
		mat = Matrix(self.content)
		fac = Matrix.identity(mat.m)
		inv = Matrix.identity(self.m)
		good = True
		matList = [Matrix(mat)]
		posList = []
		while min(mat.content[0][1:-1]) < 0 and good:
			pos = mat.selectPivMax()
			if pos[0] == False:
				good = False
				print('May have stopped preemptively.')
			else:
				mats = mat.makePiv(pos[0],pos[1])
				posList.append(list(pos))
				mat = mats[0].matMult(mat)
				inv = mats[0].matMult(inv)
				fac = fac.matMult(mats[1])
				matList.append(Matrix(mat))
		return [mat, fac, inv, matList, posList]
	
	def simplexAlgMaxIter(self):
		pos = self.selectPivMax()
		mats = self.makePiv(pos[0],pos[1])
		return mats[0].matMult(self)
	
	def simplexAlgMin(self):
		mat = Matrix(self.content)
		fac = Matrix.identity(mat.m)
		inv = Matrix.identity(self.m)
		good = True
		matList = [Matrix(mat)]
		posList = []
		while max(mat.content[0][1:-1]) > 0 and good:
			pos = mat.selectPivMin()
			if pos[0] == False:
				good = False
				print('May have stopped preemptively.')
			else:
				mats = mat.makePiv(pos[0],pos[1])
				posList.append(list(pos))
				mat = mats[0].matMult(mat)
				inv = mats[0].matMult(inv)
				fac = fac.matMult(mats[1])
				matList.append(Matrix(mat))
		return [mat, fac, inv, matList, posList]
	
	def simplexAlgMinIter(self):
		pos = self.selectPivMin()
		mats = self.makePiv(pos[0],pos[1])
		return mats[0].matMult(self)
	
	def valListFromRREF(self):
		values = list()
		for i in range(self.n - 1):
			zeros = list(map(lambda j: self.content[j][i], range(self.m))).count(0)
			if zeros == self.m - 1:
				row = Utils.firstTrue(list(map(lambda j: self.content[j][i], range(self.m))), lambda i: i != 0)
				val = Fraction(self.content[row][self.n - 1], self.content[row][i])
			elif zeros == self.m:
				val = 'parameter'
			else:
				val = 0
			values.append(val)
		return values
	
	def valListFromSimplex(self): #Note:  This assumes the matrix has a pivot for each row.
		values = [0] * (self.n - 1)
		for i in range(self.m):
			col = Utils.firstTrue(list(map(lambda j: self.isSimPiv([i, j]), range(self.n - 1))), lambda j: j)
			if col < self.n - 1:
				values[col] = self.calcPivVal([i, col])
			elif self.content[i][-1] != 0:
				raise Exception('Given Matrix is in an invalid simplex configuration.')
		return values
	
	def extendBelow(self, mat):
		if self.n != mat.n:
			raise IndexError('Matricies must have the same number of collumns.')
		data = list(self.content)
		data.extend(mat.content)
		return Matrix(data)
	
	def extendRight(self, mat):
		if self.m != mat.m:
			raise IndexError('Matricies must have the same number of rows.')
		data1 = [[self.content[i][j] for j in range(self.n)] for i in range(self.m)]
		data2 = mat.content
		for i in range(self.m):
			data1[i].extend(data2[i])
		return Matrix(data1)
	
	def pivBuilderBad(self):  #This function is stupid.  It makes a pivot in every collumn it can until every row has a pivot.
		mat = Matrix(self)
		fac = Matrix.identity(mat.m)
		inv = Matrix.identity(self.m)
		needPiv = [True] * (mat.m - 1)
		matList = [Matrix(mat)]
		posList = []
		#for i in range(mat.m - 1):
		#	if mat.content[i + 1][-1] == 0:
		#		needPiv[i] = False
		#		col = Utils.firstTrue(mat.content[i + 1], lambda j: j != 0)
		#		if col < mat.n:
		#			mats = mat.makePiv(i + 1, col)
		#			mat = mats[0].matMult(mat)
		#			inv = mats[0].matMult(inv)
		#			fac = fac.matMult(mats[1])
		#			matList.append(mat)
		#			posList.append([i + 1, col])
		good = True
		#stallCheck = [Matrix([[]])] * (mat.m - 1)
		row = 1
		col = 0
		cI = 0
		while good and any(needPiv):
			if row == mat.m:
				row = 1
			if mat.content[row][-1] == 0 and needPiv[row - 1]:
				#input()
				#mat.matPrint()
				needPiv[row - 1] = False
				col = Utils.firstTrue(mat.content[row], lambda j: j != 0)
				if col < mat.n - 1:
					mats = mat.makePiv(row, col)
					mat = mats[0].matMult(mat)
					inv = mats[0].matMult(inv)
					fac = fac.matMult(mats[1])
					matList.append(mat)
					posList.append([row, col])
			else:
				#row = Utils.firstTrue(needPiv) + 1
				#col = mat.rowSelPiv(row)
				#print(mat.content[row][i])
				#print(needPiv)
				#print(i)
				#mat.matPrint()
				#row = mat.selectPiv(i)
				#print(row)
				#input()
				#if col != False:
				if needPiv[row - 1]:
					#input()
					#mat.matPrint()
					#print(row)
					valCols = list(filter(lambda i: mat.content[row][i] > 0, range(self.n - 1)))
					#print(valCols)
					if cI >= len(valCols) - 1:
						cI = 0
					else:
						cI += 1
					#print(cI)
					if len(valCols) > 0:
						col = valCols[cI]
						#print(col)
						tRow = mat.selectPiv(col)
						if tRow != False:
							if mat.content[row][col] != 0:
								if mat.calcPivVal([row, col]) == mat.calcPivVal([tRow, col]):
									tRow = row
							#print(tRow)
							needPiv[tRow - 1] = False
							#print([tRow,col])
							mats = mat.makePiv(tRow, col)
							#mats[0].matPrint()
							#mats[0].matMult(mat).matPrint()
							mat = mats[0].matMult(mat)
							inv = mats[0].matMult(inv)
							fac = fac.matMult(mats[1])
							matList.append(mat)
							posList.append([tRow, col])
					else:
						#if stallCheck[row - 1].content == mat.content:
						good = False
						#else:
						#	stallCheck[row - 1] = Matrix(mat)
			row += 1
		#if any(needPiv):
		#	print('Pivots could not be found for every non-trivial row.')
		return [mat, fac, inv, matList, posList, not any(needPiv)]
	
	def pivBuilder(self):
		mat = Matrix(self)
		fac = Matrix.identity(mat.m)
		inv = Matrix.identity(self.m)
		needPiv = [True] * (mat.m - 1)
		matList = [Matrix(mat)]
		posList = []
		working = True
		while working:
			working = False
			for i in range(mat.m - 1):
				if mat.content[i + 1][-1] == 0 and needPiv[i]:
					needPiv[i] = False
					col = Utils.firstTrue(mat.content[i + 1], lambda j: j != 0)
					if col < mat.n:
						mats = mat.makePiv(i + 1, col)
						mat = mats[0].matMult(mat)
						#mat.matPrint()
						#print([i+1, col])
						inv = mats[0].matMult(inv)
						fac = fac.matMult(mats[1])
						matList.append(mat)
						posList.append([i + 1, col])
						working = True
			good = True
			col = 1
			while col < (mat.n - 1) and any(needPiv):
				row = mat.selectPiv(col)
				if row != False:
					if not needPiv[row - 1]:
						i = Utils.firstTrue(range(mat.m - 1), lambda j: False if mat.content[j + 1][col] == 0 else (needPiv[j] and (mat.calcPivVal([row, col]) == mat.calcPivVal([j + 1, col])))) + 1
						if i < mat.m:
							row = i
					if needPiv[row - 1]:
						needPiv[row - 1] = False
						mats = mat.makePiv(row, col)
						mat = mats[0].matMult(mat)
						#mat.matPrint()
						#print([row, col])
						inv = mats[0].matMult(inv)
						fac = fac.matMult(mats[1])
						matList.append(mat)
						posList.append([row, col])
						col = 0
						working = True
				col += 1
		return [mat, fac, inv, matList, posList, not any(needPiv)]
	
	def isSimPiv(self, pos):
		good = True
		for i in range(self.m):
			#print(self.content[i][pos[1]], self.content[i][pos[1]] == 0, ':', i, i == pos[0])
			if (self.content[i][pos[1]] != 0) != (i == pos[0]):
				good = False
		if good:
			if self.content[pos[0]][pos[1]] < 0:
				good = False
		return good
	
	def calcPivVal(self, pos):
		#if self.content[pos[0]][pos[1]] == 0:
		#	return False
		#else:
		return Fraction(self.content[pos[0]][-1], self.content[pos[0]][pos[1]])
	
	#def possiblePivLocs(self):
	#	possibleLocs = list()
	#	for i in range(self.n - 1):
	#		location = list(filter(lambda j: self.content[j][i] != 0, range(self.m)))
	#		if len(location) == 1:
	#			possibleLocs.append([location[0],i)
	#	return possibleLocs
	
	"""def simplexMatFromConstraints(constraints, weights = None, ObjVar = 'w', maximize = False, ObjEqn = None):  #Constraints come in form: [coeffs, names, form]
		newNames = ['', ObjVar]
		if ObjEqn == None:
			ObjEqn = [[1],[ObjVar],'']
		newNames = Utils.unionLists(newNames, ObjEqn[1])
		rows = len(constraints)
		for i in range(rows):
			newNames = Utils.unionLists(newNames, constraints[i][1])
			#print(newNames)
		newObjEqn = EqnUtils.coeffReAlign(ObjEqn[0], ObjEqn[1], newNames)[0]
		newObjEqn = list(map(lambda i: Fraction(i, newObjEqn[1]), newObjEqn))
		data = [[]] * rows
		b = [[0]] * rows
		revConstr = [False] * rows
		for i in range(rows):
			rowList = EqnUtils.coeffReAlign(constraints[i][0], constraints[i][1], newNames)[0]
			if rowList[0] > 0:
				rowList = list(map(lambda i: -i, rowList))
				revConstr[i] = True
			bEntry = rowList.pop(0)
			data[i] = rowList
			b[i] = [-bEntry]
			#print(b)
		A = Matrix(data)
		cols = A.n
		fullMat = A.extendRight(Matrix.identity(rows)).extendRight(Matrix.identity(rows).scalMult(-1))
		LP = fullMat.extendRight(Matrix(b))
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
		unrectifiedLP = Matrix([zRow]).extendBelow(LP)  #At this point, the unrectified goal completion LP is ready.
		#unrectifiedLP.matPrint()
		fac = Matrix.identity(unrectifiedLP.m)
		inv = Matrix.identity(unrectifiedLP.m)
		for i in range(rows):
			mats = unrectifiedLP.makePiv(i + 1, i + 1 + cols)
			inv = mats[0].matMult(inv)
			fac = fac.matMult(mats[1])
		return [unrectifiedLP, LP, fac, inv]"""

"""class SimplexRows:
	def __init__(input, devVarName = '.'):
		listInput = list();
		if type(input) == type(list()):
			listInput = list(input)
		else:
			listInput = [input]
		#input should be in form [[coeffs1,names1,form1],[coeffs2,names2,form2]...]
		newNames = ['']
		for i in range(len(input)):
			newNames = Utils.unionLists(newNames,input[i][1])
		for i in range(len(input)):
			newNames.append(devVarName + str(i) + '+')"""

class Utils:
	def boolNum(i):
		if i:
			return 1
		else:
			return 0
	
	def kDel(i,j):
		return Utils.boolNum(i == j)
	
	def firstTrue(i, condition = bool):
		found = False
		j = 0
		while found == False and j < len(i):
			if condition(i[j]):
				found = True
			else:
				j += 1
		return j
	
	def pivIndex(i):
		return Utils.firstTrue(i, lambda j: j != 0)
	
	def minIndex(i, f = None):
		if f == None:
			f = (lambda i: i)
		return min(range(len(i)), key = lambda j: f(i[j]))
	
	def maxIndex(i, f = None):
		if f == None:
			f = (lambda i: i)
		return max(range(len(i)), key = lambda j: f(i[j]))
	
	def lenCheck(i1, i2, name1, name2):
		if len(i1) != len(i2):
			raise IndexError('The number of ' + name1 + ' does not match the number of ' + name2 +'!')
	
	def unionLists(oldList, newList):
		outList = list(oldList)
		for item in newList:
			if item not in outList:
				outList.append(item)
		return outList
	
	def isInt(num):
		return int(num) == num

class EqnUtils:
	def eqnFromIneq(ineq, name):
		chars = ineq.split('')
		eqInd = Utils.firstTrue(chars, lambda i: i == '=')
		form = chars[eqInd - 1]
		if form == '!':
			print ('"!=", or "not equal to" is not supported.')
		elif form == '<':
			chars[eqInd - 1] = '+' + name
		elif form == '>':
			chars[eqInd - 1] = '-' + name
		return ''.join(chars)
	
	def dataFromEqn(ineq):
		chars = list(ineq)
		chars = list(filter(lambda i: i != ' ', chars))
		names = ['']
		coeffs = [0]
		pastEq = False
		form = ''
		char = chars.pop(0)
		#print(char + ' 1')
		while len(chars) > 0:
			tempString = ''
			tempNumber = ''
			sign = 1
			while not (char.isalnum() or char == '.' or char == ''):
				if char == '-':
					sign *= -1
				elif char == '<' or char == '>':
					form = char
				elif char == '=':
					pastEq = True
				if len(chars) == 0:
					char = ''
				else:
					char = chars.pop(0)
					#print(char + ' 2')
			while char.isnumeric() or char == '.' or char == '/':
				tempNumber += char
				if len(chars) == 0:
					char = ''
				else:
					char = chars.pop(0)
					#print(char + ' 3')
			if char == '*':
				char = chars.pop(0)
				#print(char + ' 4')
			while char.isalnum() or char == '.':
				tempString += char
				if len(chars) == 0:
					char = ''
				else:
					char = chars.pop(0)
					#print(char + ' 5')
			if tempNumber == '':
				tempNumber = '1'
			tempNumber = Fraction(tempNumber) * sign
			if pastEq:
				tempNumber *= -1
			pos = Utils.firstTrue(names, lambda i: i == tempString)
			if pos == len(names):
				names.append(tempString)
				coeffs.append(tempNumber)
			else:
				coeffs[pos] += tempNumber
		return [coeffs, names, form]
	
	def coeffReAlign(coeffs, names, newNames):
		Utils.lenCheck(coeffs, names, 'coefficients', 'variable names')
		newCoeffs = [0] * len(newNames)
		for i in range(len(names)):
			j = Utils.firstTrue(newNames, lambda k: k == names[i])
			newCoeffs[j] += coeffs[i]
		return [newCoeffs, newNames]
	
	def eqnFromData1(coeffs, names, form):
		Utils.lenCheck(coeffs, names, 'coefficients', 'variable names')
		valuesL = []
		valuesR = []
		for i in range(len(names)):
			val = coeffs[i]
			term = str(abs(val)) + names[i]
			if val < 0:
				valuesR.append(term)
			elif val > 0:
				valuesL.append(term)
		return (' + '.join(valuesL) + form + '=' + ' + '.join(valuesR))
	
	def eqnFromData2(coeffs, names, form):
		Utils.lenCheck(coeffs, names, 'coefficients', 'variable names')
		eqn = ''
		const = 0
		blank = True
		for i in range(len(names)):
			neg = False
			val = coeffs[i]
			name = names [i]
			if name == '' or val == 0:
				const -= val
			else:
				if val < 0:
					neg = True
				if blank:
					blank = False
					if neg:
						eqn += '-'
				else:
					if neg:
						eqn += ' - '
					else:
						eqn += ' + '
				eqn += (str(abs(val)) + name)
		return (eqn + ' ' + form + '= ' + str(const))
	
	def printMeaning(tempValues, tempNames = None):
		if type(tempValues) == type(list()):
			if tempNames == None:
				raise TypeError('If values is a list, then names must be provided.')
			Utils.lenCheck(tempValues, tempNames, 'values', 'variables')
			values = tempValues
			names = tempNames
		elif type(tempValues) == type(dict()):
			values = list()
			names = list()
			for name in tempValues:
				names.append(name)
				values.append(tempValues[name])
		msg = ''
		for i in range(len(names)):
			if i != 0:
				msg += '\n'
			msg += names[i] + ' = ' + str(values[i])
		print(msg)
	
	def eqFromIneq(ineq, name = '.', devVarName = None): #ineq = [coeffs, names, form]
		coeffs = list(ineq[0])
		names = list(ineq[1])
		form = str(ineq[2])
		if form == '<':
			names.append(name + '+')
			coeffs.append(Fraction(1))
		if form == '>':
			names.append(name + '-')
			coeffs.append(Fraction(-1))
		if devVarName != None:
			if form != '<':
				names.append(devVarName + '+')
				coeffs.append(Fraction(1))
			if form != '>':
				names.append(devVarName + '-')
				coeffs.append(Fraction(-1))
		return [coeffs, names, '']




















