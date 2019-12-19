class Node:
	def __init__(self, name, preReqs, duration, requires = []):
		self.name = name
		self.preReqs = preReqs
		self.duration = duration
		self.ES = None
		self.LS = None
		self.EF = None
		self.LF = None
		self.successors = set()
		self.TS = None
		self.FS = None
	
	def addSuccessor(self, successor):
		self.successors.add(successor)
	
class CPM:
	def __init__(self, nodeList = []):
		self.nodes = dict()
		for node in nodeList: #These are Node objects
			self.nodes[node.name] = node
	
	def update(self, terminal = None):
		self.updateEarly()
		self.updateSuccessors()
		self.updateLate(terminal)
		self.updateSlack()
	
	def resetNodes(self):  #Note:  This replaces all nodes within the CPM
		for i in self.nodes:
			node = self.nodes[i]
			self.nodes[i] = Node(node.name, node.preReqs, node.duration, node.requires)
	
	def updateSuccessors(self):
		for node in self.nodes: #This updates the successors of the nodes
			preReqs = self.nodes[node].preReqs
			for req in preReqs:
				self.nodes[req].addSuccessor(node)
	
	def updateEarly(self):
		searching = set()
		def ES(node):
			if self.nodes[node].ES == None:
				if len(self.nodes[node].preReqs) == 0:
					self.nodes[node].ES = 0
				else:
					self.nodes[node].ES = max(map(EF, self.nodes[node].preReqs))
			return self.nodes[node].ES
		def EF(node):
			if self.nodes[node].EF == None:
				if node in searching:
					raise Exception('Cyclical reference while finding earlyStart')
				else:
					searching.add(node)
				self.nodes[node].EF = ES(node) + self.nodes[node].duration
				searching.remove(node)
			return self.nodes[node].EF
		for node in self.nodes:
			EF(node)
	
	def updateLate(self, terminal = None): #Run after successors have been defined ( and updateEarly, if terminal not given).
		searching = set()
		if terminal == None:
			terminal = self.getEF()
		def LF(node):
			if self.nodes[node].LF == None:
				if len(self.nodes[node].successors) == 0:
					self.nodes[node].LF = terminal
				else:
					self.nodes[node].LF = min(map(LS, self.nodes[node].preReqs))
			return self.nodes[node].LF
		def LS(node):
			if self.nodes[node].LS == None:
				if node in searching:
					raise Exception('Cyclical reference while finding lateStart')
				else:
					searching.add(node)
				self.nodes[node].LS = LF(node) - self.nodes[node].duration
				searching.remove(node)
			return self.nodes[node].LS
		for node in self.nodes:
			LS(node)
	
	def getEF(self):
		return self.nodes[max(self.nodes, key = lambda i: self.nodes[i].EF)].EF
	
	def getTerminalNodes(self):
		terminal = self.getEF()
		return set(filter(lambda i: self.nodes[i].EF == terminal, self.nodes))
	
	def updateSlack(self): #Run after updateLate
		for i in self.nodes:
			node = self.nodes[i]
			node.TS = node.LF - node.EF
			node.FS = min(map(lambda i: self.nodes[i].ES, node.successors)) - node.EF
	
	def critNodes(self):
		return set(filter(lambda i: self.nodes[i].TS == 0, self.nodes))
	
	def psuedoCrit(self):
		return set(filter(lambda i: self.nodes[i].FS == 0, self.nodes))
	
	def getLP(self, broken = False, allowPartial = False, objVar = 'Z', commonVar = 'x'):
		eqnList = []
		binList = set()
		lockedNodes = self.critNodes()
		looseNodes = set(self.nodes) - self.critNodes()
		if broken:
			ranges = dict()
			for node in looseNodes:
				ranges[node] = range(self.nodes[node].ES, self.nodes[node].LF)
				nodeEq = [[-self.nodes[node].duration],[''],'']
				for i in ranges[node]:
					nodeEq[0].append(1)
					nodeEq[1].append(commonVar + '.' + node + '.' + str(i))
					binList.add(commonVar + '.' + node + '.' + str(i))
				eqnList.append(nodeEq)
				
		else:
			ranges = dict()
			for node in looseNodes:
				ranges[node] = range(self.nodes[node].ES, self.nodes[node].LS)
				nodeEq = [[-1],[''],'']
				for i in ranges[node]:
					nodeEq[0].append(1)
					nodeEq[1].append(commonVar + '.' + node + '.' + str(i))
					binList.add(commonVar + '.' + node + '.' + str(i))
				eqnList.append(nodeEq)
				



















