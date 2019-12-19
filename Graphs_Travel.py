from Utils import falseIndexible, square, housing, plotLine, defCallDict, defValDict
import math
from SymmetricGroups1 import trans, compose, identity

class badOrientableVertexGraph(object): #considered bad because it makes so many vertex objects, which could simply be lists.
	
	def __init__(self, vOrder = None):
		self.vOrder = vOrder
		self.verticies = list()
	
	def newVertex(self, adjs = None):
		vert = badOrientableVertex(self, adjs, self.vOrder)
		self.verticies.append(vert)
		return vert

class badOrientableVertex(object):
	
	def __init__(self, graph, adjs = None, order = None):
		if adjs is None:
			adjs = list()
		if order is None:
			order = len(adjs)
		else:
			adjs.extend([None] * (order - len(adjs)))
		self.g = graph
		self.n = order
		self.adjs = adjs

class OrientableVertexGraph(object): #Not to be confused with orientable graph, here each vertex has a sequence for the verticies it is connected to.
	
	def __init__(self, data = None):
		if data is None:
			data = list()
		elif isinstance(data, badOrientableVertexGraph):
			inds = dict()
			nData = list()
			i = 0
			for vertex in data.verticies:
				inds[vertex] = i
				nData.append(map(lambda i: inds[i], vertex.adjs)) #sneaky.  the mappings require inds to be filled prior to evaluation, so the mappings are created here, but not evaluated until the loop is over.
			data = [list(adjs) for adjs in nData]
		self.data = tuple(map(tuple, data)) #List of lists.  each list represents a vertex, the contents of the list being the indicies of the adjacent verticies.
	
	def vertex(self, n):
		return OrientableVertex(self, n, self.data[n])
	
	def __hash__(self):
		return hash(self.data)
	
	def __eq__(self, other): #todo: check equality up to isomorphism.
		if type(self) != type(other): return False
		return self.data == other.data

class Graph(object): #Not to be confused with orientable graph, here each vertex has a sequence for the verticies it is connected to.
	
	def __init__(self, data = None):
		if data is None:
			data = list()
		elif isinstance(data, (OrientableVertexGraph)):
			data = data.data
		elif isinstance(data, badGraph):
			inds = dict()
			nData = list()
			i = 0
			for vertex in data.verticies:
				inds[vertex] = i
				nData.append(map(lambda i: inds[i], vertex.adjs)) #sneaky.  the mappings require inds to be filled prior to evaluation, so the mappings are created here, but not evaluated until the loop is over.
			data = [list(adjs) for adjs in nData]
		self.data = tuple(map(frozenset, data)) #List of lists.  each list represents a vertex, the contents of the list being the indicies of the adjacent verticies.
	
	def vertex(self, n):
		return Vertex(self, n, self.data[n])
	
	def __hash__(self):
		return hash(self.data)
	
	def __eq__(self, other): #todo: check equality up to isomorphism.
		if type(self) != type(other): return False
		return self.data == other.data

class OrientableVertex(object):
	
	def __init__(self, graph, n, adjs):
		self.graph = graph
		self.ind = n
		self._adjs = adjs
		self.order = len(adjs)
		self.adjs = falseIndexible(lambda i: self.graph.vertex(self._adjs[i]))
	
	def __hash__(self):
		return hash((self.ind, self.graph))
	
	def __eq__(self, other):
		if type(self) != type(other): return False
		return (self.ind == other.ind) and (self.graph == other.graph)

class Vertex(object):
	
	def __init__(self, graph, n, adjs):
		self.graph = graph
		self.ind = n
		self._adjs = adjs
		self.order = len(adjs)
	
	def __hash__(self):
		return hash((self.ind, self.graph))
	
	def __eq__(self, other):
		if type(self) != type(other): return False
		return (self.ind == other.ind) and (self.graph == other.graph)

def altCoerceTransitivity(graph, E = None, correctionInfo = None): #E must be an involution permutation.
	data = list(graph.data)
	if not data: return graph #Why you'd give it an empty graph I have no idea.
	order = len(data[0])
	e = identity(order)
	if E is None: E = e
	else: assert len(E) == order
	assert compose(E, E) == e
	# fixed = defCallDict(set)
	avail = defCallDict(lambda: set(range(order)))
	corrections = defValDict(e)
	for v in range(len(data)):
		#avail[v].difference_update(range(order))# Processed verticies are always fixed.  Fixed values are the indicies of adjs, those which are available are not fixed.
		print(v, avail[v], data[v])
		while avail[v]:
			ind = min(avail[v], key = lambda i: len(avail[data[v][i]]))
			assert ind in avail[v]
			adj = data[v][ind]
			print('\t', adj, avail[adj], data[adj])
			temp = ((i, E[i]) for i in range(order) if i in avail[v])
			merging = max((k for k in temp if k[1] in avail[adj]), key = lambda i: i[1])
			sC = trans(merging[0], ind, order)
			oC = trans(merging[1], data[adj].index(v), order)
			corrections[v] = compose(corrections[v], sC)
			corrections[adj] = compose(corrections[adj], oC)
			data[v] = tuple(compose(data[v], sC))
			data[adj] = tuple(compose(data[adj], oC))
			avail[v].remove(merging[0])
			avail[adj].remove(merging[1])
			print('\t\t', merging)
	if correctionInfo is not None:
		correctionInfo.val = corrections
	return OrientableVertexGraph(data)

def coerceOrientation(graph):
	data = graph.data
	if not data: return OrientableVertexGraph()
	order = len(data[0])
	nData = list()
	unOriented = list(map(set, data))
	freeInds = list(set(range(order)) for v in data)
	

class VertexOrientation(object):
	
	def __init__(self, vertex, prev):
		self.vertex = vertex
		self.orientation = vertex._adjs.index(prev)
	
	def uTravel(self, tNumber):
		return VertexOrientation(self.vertex.adjs[(self.orientation + tNumber) % self.vertex.order], self.vertex.ind)
	
	def travel(self, arg = None, *args):
		if arg is None: return self
		return self.uTravel(arg).travel(*args)# Notice that this will be evaluated right-to-left, in accordance with function composition conventions.
	
	def tOrder(self, tNumber): # Only perform on finite graphs.
		acc = 1
		tgt = self.uTravel(tNumber)
		while tgt != self:
			acc += 1
			tgt = tgt.uTravel(tNumber)
		return acc
	
	def __eq__(self, other):
		if type(self) != type(other): return False
		return (self.vertex == other.vertex) and (self.orientation == other.orientation)
	
	def __hash__(self):
		return hash((self.vertex, self.orientation))

class TravelGroup(object):
	
	def __init__(self, restrictions):
		self.rest = restrictions

def lPlot(graph): #Plots a graph with all the verticies in a line.
	pPlots = list()
	nPlots = list()
	for vert, adjs in enumerate(graph.data):
		for adj in adjs:
			edge = 'sqrt(' + str(sqare(vert - adj)/4) + ' - (x - ' + str((vert + adj)/2) + ')^2)'
			if vert < adj:
				pPlots.append(edge)
			else:
				nPlots.append(edge)

def cPlot(graph): #Plots an undirected graph with all the verticies on a unit circle
	n = len(graph.data)
	verts = [(math.cos(2*k*math.pi/n), math.sin(2*k*math.pi/n)) for k in range(n)]
	edges = list()
	for vert, adjs in enumerate(graph.data):
		for adj in adjs:
			if adj < vert: continue
			R = housing()
			edge = plotLine(verts[vert], verts[adj], R)
			r, = R



































