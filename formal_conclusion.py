from isTautology import *

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

def A1(F,G): return '('+F+IMP+'('+G+IMP+F+')'+')'
def A2(F,G,H): return '('+'('+F+IMP+'('+G+IMP+H+')'+')'+IMP+'('+'('+F+IMP+G+')'+IMP+'('+F+IMP+H+')'+')'+')'
def A3(F,G): return '('+'('+'('+NEG+G+')'+IMP+'('+NEG+F+')'+')'+IMP+'('+'('+'('+NEG+G+')'+IMP+F+')'+IMP+G+')'+')'

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
    Conclusion = [  A3('('+NEG+'('+F+')'+')',F),
                    TL('('+NEG+'('+F+')'+')'),
                    S2('(('+NEG+'('+F+')'+')'+IMP+'('+NEG+'('+NEG+'('+F+')'+')'+'))','('+'('+NEG+'('+F+')'+')'+IMP+'('+NEG+'('+F+')'+')'+')',F),
                    A1('('+NEG+'('+NEG+'('+F+')'+'))','('+NEG+'('+F+')'+')'),
                    S1('('+NEG+'('+NEG+'('+F+')'+'))','(('+NEG+'('+F+')'+')'+IMP+'('+NEG+'('+NEG+'('+F+')'+')'+'))',F)]
    return [[],Conclusion[4][1]]

def T2(F):
    return [[],'('+F+IMP+'('+NEG+'('+NEG+'('+F+')'+')'+'))']
def T3(F,G):
    return [[],'('+'('+NEG+'('+F+')'+')'+IMP+'('+F+IMP+G+')'+')']
def T4(): pass
def T5(): pass
def T6(F,G):
    return [[],'('+F+IMP+'('+'('+NEG+'('+G+')'+')'+IMP+'('+NEG+'('+F+IMP+G+')'+')'+')'+')']
def T7(F,G):
    return [[],'('+'('+F+IMP+G+')'+IMP+'('+'('+'('+NEG+F+')'+IMP+G+')'+IMP+G+')'+')']

def TL(F):
    F1 = A2(F,'('+F+IMP+F+')',F)
    F2 = A1(F,'('+F+IMP+F+')')
    F3 = modus_ponens(F2,F1)
    F4 = A1(F,F)
    F5 = modus_ponens(F4,F3)
    return F5

def modus_ponens(A,B):
    if A == B[1:len(A)+1]: return B[len(A)+2:len(B)-1]

def is_modus_ponens(A,P,Q): return A == modus_ponens(P,Q)

def deduction_theorem(Hypothesys,F,G,Conclusion):
    if Conclusion == True:
        return [Hypothesys,'('+F+IMP+G+')']
    for i in range(len(Conclusion)):
        if i == 0:
            if Conclusion[0] == F: D = TL(F)
            else:
                F11 = A1(Conclusion[i],F)
                D = modus_ponens(Conclusion[i],F11)
        else:
            T = True
            for p in range(i):
                for q in range(i):
                    if is_modus_ponens(Conclusion[i],Conclusion[p],Conclusion[q]):
                        F12 = A2(F,Conclusion[p],Conclusion[i])
                        D = modus_ponens('('+F+IMP+Conclusion[q]+')',F12)
                        D = modus_ponens('('+F+IMP+Conclusion[p]+')',D)
                        T = False
            if T and Conclusion[i] == F: D = TL(F)
            elif T:
                F11 = A1(Conclusion[i],F)
                D = modus_ponens(Conclusion[i],F11)
    return (Hypothesys,D)

def kalmar_lemma(F,alpha):
    S = sub_formulas(F)
    _arity = arity(F)
    x = [0]*_arity[0]
    for i in range(_arity[1]):
        if alpha[i] == 1:
            x[i] = '(x['+str(_arity[2][i])+'])'
        elif alpha[i] == 0:
            x[i] = '('+NEG+'(x['+str(_arity[2][i])+']))'
    if S[1] == 0: return [x,F,alpha]
    elif S[1] == 1:
        if calc(adoptate(F),alpha) == 1: return [x,F,alpha]
        elif calc(adoptate(F),alpha) == 0:
            G = kalmar_lemma(sub_formulas(F)[0][0],alpha)[1]
            F1 = T2(G)[1]
            F2 = modus_ponens(G,F1)
            return [x,F2[2:len(F2)-1],alpha]
    elif S[1] == 2:
        G = kalmar_lemma(sub_formulas(F)[0][0],alpha)[1]
        H = kalmar_lemma(sub_formulas(F)[0][1],alpha)[1]
        if calc(adoptate(G),alpha) == 0:
            F1 = T3(G,H)[1]
            F2 = modus_ponens('('+NEG+'('+G+')'+')',F1)
            return [x,F2,alpha]
        elif calc(adoptate(H),alpha) == 1:
            F1 = A1(H,G)
            F2 = modus_ponens(H,F1)
            return [x,F2,alpha]
        else:
            F1 = T6(G,H)[1]
            F2 = modus_ponens(G,F1)
            F3 = modus_ponens('('+NEG+'('+H+')'+')',F2)
            return [x,F3[2:len(F3)-1],alpha]

def adequacy_theorem(F):
    if not isTautology(F): return None
    _arity = arity(F)[0]
    for j in range(_arity):
        XA = []
        for i in range(2**(j+1)):
            alpha = [0]*_arity
            v = str(bin(i))[2:]
            for l in range(len(v)):
                alpha[l] = int(v[len(v)-l-1])
            alpha = list(reversed(alpha))
            Kalmar = kalmar_lemma(F,alpha)
            XA.append(deduction_theorem(Kalmar[0][:(_arity-j-1)],Kalmar[0][(_arity-j-1)],F,True)[1])
        XA = list(sorted(list(set(XA))))
        F1 = T7('(x['+str(_arity-j-1)+'])',F)[1]
        F2 = modus_ponens(XA[1],F1)
        F3 = modus_ponens(XA[0],F2)
    return [[],F3]

if __name__ == '__main__':
    F = format(input('F:'))
    if isTautology(F):
        C = adequacy_theorem(F)
        print(C)
    else: print('F is not tautology')
