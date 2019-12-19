from SymmetricGroups1 import *

#Factor, n = 48; 0-7 U, 8-15 F, 16-23 R, 24-31 D, 32-39 B, 40-47 L;

def cycle(t, n):
	s = list(range(n))
	for i in range(len(t)): s[t[i-1]] = t[i]
	return s

def fG(s):
	return compose(cycle([s + 2 * i for i in range(4)], 48), cycle([s + 2 * i + 1 for i in range(4)], 48))

U = fG(0)
F = fG(8)
R = fG(16)
D = fG(24)
B = fG(32)
L = fG(40)

faces = [fG(8 * i) for i in range(6)]

identity = list(range(48))

def dNumber(s):
	acc = 0
	for i in range(len(s)):
		if i = s[i]: acc += 1
	return acc

def greedyStep(s):
	