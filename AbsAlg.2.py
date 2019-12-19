"""#Function - based math and logic

Logic = {'False','True'}

And = {(('False','False'),'False'),(('False','True'),'False'),(('True','False'),'False'),(('True','True'),'True')}

Or = {(('False','False'),'False'),(('False','True'),'True'),(('True','False'),'True'),(('True','True'),'True')}

Implies = {(('False','False'),'True'),(('False','True'),'True'),(('True','False'),'False'),(('True','True'),'True')}

Equals = {(('False','False'),'True'),(('False','True'),'False'),(('True','False'),'False'),(('True','True'),'True')}

Not = {('True','False'),('False','True')}

def Prove(statement, assumptions):"""

class AbstractInitable(object):
	
	def __init__(self, **kwargs):
		for key in kwargs:
			setattr(self, key, kwargs[key])

class AbstractSet(AbstractInitable):
	
	def __contains__(self, elem):
		if hasattr(self, 'output'):
			if 'output'
		return self.contCheck(elem)

Logic = AbstractSet(elements = 

class Function(AbstractInitable):
	
	input = set()
	
	output = set()