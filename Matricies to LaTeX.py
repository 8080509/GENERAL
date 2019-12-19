import Matrix_Utils as m

def bMatrix(mat):
	msg = "\\begin{bmatrix}\n"
	for row in mat.content:
		msg += ' & '.join(map(lambda i: str(i), row)) + '\\\\\n'
	return msg + "\\end{bmatrix}"