
import asyncio as asy

class asyncIter:
	
	def __init__(self):
		self.item = None
		self.itemSet = False
		self.cond = asy.Condition()
		self.stop = None
	
	def __aiter__(self): return self
	
	async def __anext__(self):
		cond = self.cond
		async with cond:
			while not self.itemSet:
				await cond.wait()
			if self.stop is not None:
				raise self.stop
			self.itemSet = False
			cond.notify()
			return self.item
	
	async def feed(self, val):
		cond = self.cond
		async with cond:
			while self.itemSet:
				await cond.wait()
			self.itemSet = True
			cond.notify()
			self.item = val
	
	async def terminate(self, value = None, exception = None):
		if exception is None: exception = StopIteration(value)
		else: assert value is None
		cond = self.cond
		async with cond:
			while self.itemSet:
				await cond.wait()
			self.itemSet = True
			cond.notify()
			self.stop = exception
	
	async def feedIter(self, iterable):
		try:
			while True:
				await self.feed(next(iterable))
		except StopIteration as e: return e.value
		except:
			asy.create_task(self.terminate(exception = asy.CancelledError()))
			raise
	
	async def _from_iterable(self, iterable):
		task = asy.create_task(self.feedIter(iterable))
		await task
		await self.terminate(task.result())
	
	@classmethod
	def from_iterable(cls, iterable):
		out = cls()
		asy.create_task(out._from_iterable(iterable))
		return out

class asyncTee_in:
	
	def __init__(self, children):
		self.children = children
	
	async def feed(self, val):
		await asy.gather(*(child.feed(val) for child in self.children))
	
	async def terminate(self, value = None):
		await asy.gather(*(child.terminate(val) for child in self.children))

def asyncTee(n = 2):
	children = [asyncIter() for _ in range(n)]
	return asyncTee_in(children), children














































