from isTautology import *
from Logger import Logger

def NOT(F): return '('+NEG+F+')'
def IMPLICATION(F,G): return '('+F+IMP+G+')'

def alphicate(F,a):
	if calc(F,a) == 1:
		return F
	return NOT(F)

def sub_formulas(F):
	if F[:3] == '(x[':
		return [[F],0]
	elif '('+NEG+'(' == F[:3]:
		return [[F[2:len(F)-1]],1]
	else:
		out = []
		start = None
		for pair in get_semantic(F[1:len(F)-1]):
			if 0 in pair: start = pair
			elif start and start[1]+1 in pair: end = pair
		count = -3
		for i in range(len(F[1:len(F)-1])):
			if F[i] == ')' or F[i] == '(': count += 1
			if count == start[1]:
				start[1] = 0
				out.append(F[1:i-1])
		out.append(F[len(out[0])+2:len(F)-1])
		return [out,2]

def A1(F,G):
	P = IMPLICATION(F,IMPLICATION(G,F))
	Logger(P,'A1 for '+F+' and '+G)
	return P
def A2(F,G,H):
	P = IMPLICATION(IMPLICATION(F,IMPLICATION(G,H)),IMPLICATION(IMPLICATION(F,G),IMPLICATION(F,H)))
	Logger(P,'A2 for '+F+' and '+G+' and '+H)
	return P
def A3(F,G):
	P = IMPLICATION(IMPLICATION(NOT(G),NOT(F)),IMPLICATION(IMPLICATION(NOT(G),F),G))
	Logger(P,'A3 for '+F+' and '+G)
	return '('+'('+'('+NEG+G+')'+IMP+'('+NEG+F+')'+')'+IMP+'('+'('+'('+NEG+G+')'+IMP+F+')'+IMP+G+')'+')'

def S1(F,G,H):
	Hypothesys = ['('+F+IMP+G+')','('+G+IMP+H+')']
	Conclusion = ['('+F+IMP+G+')','('+G+IMP+H+')',F]
	P = modus_ponens(Conclusion[2],Conclusion[0])
	Conclusion.append(P)
	Q = modus_ponens(Conclusion[3],Conclusion[1])
	Conclusion.append(Q)
	return deduction_theorem(Hypothesys,F,H,Conclusion)

def S2(F,G,H):
	Hypothesys = ['('+F+IMP+'('+G+IMP+H+')'+')',G]
	Conclusion = ['('+F+IMP+'('+G+IMP+H+')'+')',G,F]
	P = modus_ponens(Conclusion[2],Conclusion[0])
	Conclusion.append(P)
	Q = modus_ponens(Conclusion[1],Conclusion[3])
	Conclusion.append(Q)
	return deduction_theorem(Hypothesys,F,G,Conclusion)

def T1(F):
	F1 = A3('('+NEG+'('+F+')'+')',F)
	F2 = TL('('+NEG+'('+F+')'+')')
	F3 = S2('(('+NEG+'('+F+')'+')'+IMP+'('+NEG+'('+NEG+'('+F+')'+')'+'))',F2,F)[1]
	F4 = A1('('+NEG+'('+NEG+'('+F+')'+'))','('+NEG+'('+F+')'+')')
	F5 = S1('('+NEG+'('+NEG+'('+F+')'+'))','('+'('+NEG+F+')'+IMP+'('+NEG+'('+NEG+F+')'+')'+')',F)[1]
	return [[],F5]

def T2(F):
	F1 = A3(F,NOT(NOT(F)))
	F2 = T1(NOT(F))[1]
	F3 = modus_ponens(F2,F1)
	F4 = A1(F2,F1)
	F5 = S1(F,IMPLICATION(NOT(NOT(NOT(F))),F),NOT(NOT(F)))[1]
	return [[],F5]
def T3(F,G):
	F1 = NOT(F)
	F2 = A1(F,NOT(G))
	F3 = modus_ponens(F,F2)
	F4 = A1(F1,NOT(G))
	F5 = modus_ponens(F1,F4)
	F6 = A3(F,G)
	F7 = modus_ponens(F5,F6)
	F8 = modus_ponens(F3,F7)
	out = deduction_theorem([F1],F,F8,[F1,F2,F3,F4,F5,F6,F7,F8])
	out = deduction_theorem([],F1,out[1],out[2])
	return [[],out[1]]
def T4(F,G):
	F1 = A3(F,G)
	F2 = IMPLICATION(NOT(G),NOT(F))
	F3 = modus_ponens(F2,F1)
	F4 = A1(F,NOT(G))
	F5 = S1(F,IMPLICATION(NOT(G),F),G)[1]
	#print(F5)
	out0 = S1(F,IMPLICATION(NOT(G),F),G)[2]
	out = [F1,F2,F3,F4]
	out.extend(out0)
	out = deduction_theorem([],F2,F5,out)
	return [[],out[1]]
def T5(F,G):
	F1 = A3(NOT(G),NOT(F))
	F2 = IMPLICATION(F,G)
	F3 = T2(G)[1]
	F4 = S1(F,G,NOT(NOT(G)))[1]
	out = S1(F,G,NOT(NOT(G)))[2]
	F5 = T1(F)[1]
	F6 = S1(NOT(NOT(F)),F,NOT(NOT(G)))[1]
	out.extend(S1(NOT(NOT(F)),F,NOT(NOT(G)))[2])
	F7 = modus_ponens(F6,F1)
	F8 = A1(NOT(G),NOT(NOT(F)))
	F9 = S1(NOT(G),IMPLICATION(NOT(NOT(F)),NOT(G)),NOT(F))[1]
	out.extend(S1(NOT(G),IMPLICATION(NOT(NOT(F)),NOT(G)),NOT(F))[2])
	out = deduction_theorem([],F2,F9,out)
	return [[],out[1]]
def T6(F,G):
	out = []
	F1 = T5(IMPLICATION(F,G),G)[1]
	F2 = deduction_theorem([],IMPLICATION(F,G),G,[F,IMPLICATION(F,G),modus_ponens(F,IMPLICATION(F,G))])[1]
	out.extend(deduction_theorem([],F,IMPLICATION(F,G),[F,IMPLICATION(F,G),modus_ponens(F,IMPLICATION(F,G))])[2])
	F3 = modus_ponens(F2,F1)
	out.append(F3)
	out = deduction_theorem([],F,F3,out)
	return [[],out[1]]
def T7(F,G):
	F1 = IMPLICATION(F,G)
	F2 = T5(F,G)[1]
	F3 = A3(F,G)
	F4 = S1(F1,IMPLICATION(NOT(G),NOT(F)),IMPLICATION(IMPLICATION(NOT(G),F),G))[1]
	out = S1(F1,IMPLICATION(NOT(G),NOT(F)),IMPLICATION(IMPLICATION(NOT(G),F),G))[2]
	F5 = modus_ponens(F1,F4)
	F6 = T4(NOT(G),F)[1]
	F7 = Sub_Lemma_For_T7(F,G)
	F8 = S1(IMPLICATION(NOT(F),G),IMPLICATION(NOT(F),NOT(NOT(G))),IMPLICATION(NOT(G),F))[1]
	out.extend(S1(IMPLICATION(NOT(F),G),IMPLICATION(NOT(F),NOT(NOT(G))),IMPLICATION(NOT(G),F))[2])
	F9 = S1(IMPLICATION(NOT(F),G),IMPLICATION(NOT(G),F),G)[1]
	out.extend(S1(IMPLICATION(NOT(F),G),IMPLICATION(NOT(G),F),G)[2])
	out = deduction_theorem([],F1,F9,out)
	return [[],out[1]]
def Sub_Lemma_For_T7(F,G):
	F1 = NOT(F)
	F2 = IMPLICATION(NOT(F),G)
	F3 = modus_ponens(F1,F2)
	F4 = T2(G)[1]
	F5 = modus_ponens(F3,F4)
	F6 = deduction_theorem([F2,F3,F4],F1,NOT(NOT(G)),[F1,F2,F3,F4,F5])[1]
	out = deduction_theorem([F2,F3,F4],F1,NOT(NOT(G)),[F1,F2,F3,F4,F5])[2]
	out = deduction_theorem([],F2,F6,out)
	return [[],out[1]]

def TL(F):
	F1 = A2(F,'('+F+IMP+F+')',F)
	F2 = A1(F,'('+F+IMP+F+')')
	F3 = modus_ponens(F2,F1)
	F4 = A1(F,F)
	F5 = modus_ponens(F4,F3)
	return F5

def modus_ponens(A,B):
	if A == B[1:len(A)+1]:
		Logger(B[len(A)+2:len(B)-1], 'Modus ponens for '+A+' and '+B)
		return B[len(A)+2:len(B)-1]

def is_modus_ponens(A,P,Q): return A == modus_ponens(P,Q)

def deduction_theorem(Hypothesys,F,G,Conclusion):
	_Conclusion = []
	for i in range(len(Conclusion)):
		if i == 0:
			if Conclusion[0] == F:
				D = TL(F)
				_Conclusion.append(D)
				#print('A',D)
			else:
				F11 = A1(Conclusion[i],F)
				D = modus_ponens(Conclusion[i],F11)
				_Conclusion.append(F11)
				_Conclusion.append(D)
				#print('B',D)
		else:
			T = True
			for p in range(i):
				for q in range(i):
					if is_modus_ponens(Conclusion[i],Conclusion[p],Conclusion[q]):
						F12 = A2(F,Conclusion[p],Conclusion[i])
						F22 = modus_ponens('('+F+IMP+Conclusion[q]+')',F12)
						D = modus_ponens('('+F+IMP+Conclusion[p]+')',F22)
						_Conclusion.append(F12)
						_Conclusion.append(F22)
						_Conclusion.append(D)
						#print('C',D)
						T = False
			if T and Conclusion[i] == F:
				D = TL(F)
				_Conclusion.append(D)
				#print('D',D)
			elif T:
				F11 = A1(Conclusion[i],F)
				D = modus_ponens(Conclusion[i],F11)
				_Conclusion.append(F11)
				_Conclusion.append(D)
				#print('E',D)
	return [Hypothesys,D,_Conclusion]

def kalmar_lemma(F,alpha):
	out = []
	if sub_formulas(F)[1] == 0:
		out.extend([alphicate(F,alpha)])
	else:
		if sub_formulas(F)[1] == 1:
			if calc(adoptate(F),alpha) == 1:
				out.extend(kalmar_lemma(sub_formulas(F)[0][0],alpha))
			else:
				out.extend(kalmar_lemma(sub_formulas(F)[0][0],alpha))
				out.append(T2(out[len(out)-1])[1])
		else:
			sF = sub_formulas(F)[0]
			if calc(adoptate(sF[0]),alpha) == 0:
				out.extend(kalmar_lemma(sF[0],alpha))
				F1 = out[len(out)-1]
				out.append(T3(sF[0],sF[1])[1])
				F2 = out[len(out)-1]
				F3 = modus_ponens(F1,F2)
				out.append(F3)
			elif calc(adoptate(sF[1]),alpha) == 1:
				out.extend(kalmar_lemma(sF[1],alpha))
				F1 = out[len(out)-1]
				F2 = A1(F1,sF[0])
				out.append(F2)
				F3 = modus_ponens(F1,F2)
				out.append(F3)
			else:
				out.extend(kalmar_lemma(sF[0],alpha))
				F1 = out[len(out)-1]
				out.extend(kalmar_lemma(sF[1],alpha))
				F2 = out[len(out)-1]
				out.append(T6(sF[0],sF[1])[1])
				F3 = out[len(out)-1]
				F4 = modus_ponens(F1,F3)
				F5 = modus_ponens(F2,F4)
				out.append(F4)
				out.append(F5)
	return out

def gen_alphas(arity):
	alphas = []
	for i in range(2**(arity)):
		alpha = [0]*arity
		v = str(bin(i))[2:]
		for l in range(len(v)):
			alpha[l] = int(v[len(v)-l-1])
		alpha = list(reversed(alpha))
		alphas.append(alpha)
	return alphas

def adequacy_theorem(F):
	if not isTautology(F): return None
	_arity = arity(F)[0]
	out = [None]*_arity
	ALPHAS = gen_alphas(_arity+1)
	for i in range(_arity):
		out[i] = kalmar_lemma(F,ALPHAS[i])
	while _arity != 0:
		ALPHAS = gen_alphas(_arity)
		for i in range(_arity):
			ALPHAS[i][len(ALPHAS[i])-1] = 1
			Hypothesys = []
			for j in range(_arity-2):
				Hypothesys.append(alphicate('(x['+str(j)+'])',ALPHAS[i]))
			T = deduction_theorem(Hypothesys,alphicate('(x['+str(_arity-1)+'])',ALPHAS[i]),F,out[i])
			F1 = T[1]
			F1_ = T[2]

			ALPHAS[i][len(ALPHAS[i])-1] = 0
			T = deduction_theorem(Hypothesys,alphicate('(x['+str(_arity-1)+'])',ALPHAS[i]),F,out[i])
			F2 = T[1]
			F2_ = T[2]

			F3 = T7('(x['+str(_arity-1)+'])',F)[1]
			F4 = modus_ponens(F1,F3)
			F5 = modus_ponens(F2,F4)

			res = F1_
			res.extend(F2_)
			res.append(F4)
			res.append(F5)
			out[i] = res
		_arity = _arity-1
	return res

if __name__ == '__main__':
	F = input('F:')
	if isTautology(format(F)): C = adequacy_theorem(format(F))
	else: print('F is not tautology')
