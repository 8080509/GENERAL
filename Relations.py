
class eqr:
	
	"""
	Class for storing equivalence relations.
	
	Equivalence relations satisfy three properties:
		 Reflexivity : x ~ x
		    Symmetry : x ~ y -> y ~ x
		Transitivity : x ~ y and y ~ z -> x ~ z
	
	
	
	eqr([restriction]) -> new empty equivalence relation
		Optional restriction field allows control over which equivalences are made.
		
	"""
	
	defaultRestriction = lambda u, v: () if u == v else None
	
	def __init__(self, restriction = defaultRestriction, parent = None):
		self.par = parent
		self.res = restriction
		self.tab = dict()
		self.cMap = dict()
		self.count = 0
		self.depth = parent.depth + 1 if parent is not None else 0
	
	@staticmethod
	def _tableGet(tab, var):
		if var not in tab: return var
		tgt = tab[var]
		tgt = vsm._tableGet(tab, tgt);
		tab[var] = tgt
		return tgt
	
	def _align(par, alignments):
		
		table = dict()
		uQueue = list()
		
		# forward pass
		
		for pair in alignments:
			u = vsm._tableGet(table, par[pair[0]])
			v = vsm._tableGet(table, par[pair[1]])
			if u == v: continue
			if par.canAlign(u, v):
				uQueue.append(u)
				table[u] = v
			elif par.canAlign(v, u):
				uQueue.append(v)
				table[v] = u
			else:
				return None
		if not uQueue: return par
		
		# reverse pass
		
		out = vsm(par)
		# out.tab.clear()
		count = 0 if par is None else par.count
		while uQueue:
			u = uQueue.pop()
			v = out[table[u]]
			out.tab[u] = v
			out.cMap[v] = out.cMapGet(v) + vsm.cMapGet(par, u) + 1 # need to figure this out correctly.
			count += 1
		out.count = count
		return out
		
	def __getitem__(self, key, predLim = None):
		if key is None: return None
		if key in self.tab: return self.tab[key]
		tgt = self.par
		while tgt is not predLim:
			if key in tgt.tab:
				val = self.__getitem__(tgt.tab[key], tgt)
				self.tab[key] = val
				return val
			tgt = tgt.par
		# self.tab[key] = key
		return key















































