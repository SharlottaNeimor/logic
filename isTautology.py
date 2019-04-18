import re

NEG = '-'
IMP = '@'

def isTautology(F):
    _arity = arity(F)
    F = adoptate(F)
    for i in range(2**(_arity)):
        x = [0]*_arity
        v = str(bin(i))[2:]
        for j in range(len(v)):
            x[j] = int(v[len(v)-j-1])
        if calc(F,x) == 0: return False
    return True

def arity(F): return max(list(map(int,re.findall(r'\d+',F))))+1

def calc(F,x): return eval(F)%2

def adoptate(F):
    F = F.replace(NEG,'1+')
    while IMP in F:
        before_IMP = len(F.split(IMP)[0])
        amount_of_brackets = -1
        for i in range(before_IMP):
            if F[i] == ')' or F[i] == '(': amount_of_brackets += 1
        semantic = get_semantic(F)
        for pair in semantic:
            if amount_of_brackets in pair: from_bracket = pair[0] - 1
            if amount_of_brackets+1 in pair: to_bracket = pair[1]
        amount_of_brackets = -1
        for i in range(len(F)):
            if F[i] == '(' or F[i] == ')': amount_of_brackets += 1
            if amount_of_brackets == from_bracket: slice_from = i + 1
            if amount_of_brackets == to_bracket: slice_to = i + 1
        body = F[slice_from:slice_to]
        count = 0
        for k in range(len(body)):
            if body[k] == IMP and count == 0:
                body = body[:k]+'*(1+'+body[k+1:]
                count = 1
        body = "1+("+body+'))'
        F = F[:slice_from] + body + F[slice_to:]
    return F

def get_semantic(F):
    semantic_string = []
    semantic = []
    for i in F:
        if i == '(' or i == ')': semantic_string.append(i)
    for i in range(len(semantic_string)):
        if semantic_string[i] == ')':
            for j in range(i):
                if semantic_string[j] == '(': m = j
            semantic.append((m,i))
            semantic_string[i] = " "
            semantic_string[m] = " "
    return semantic

if __name__ == '__main__':
    F = input('F:')
    print(isTautology(F))
