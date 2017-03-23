import copy
import re
import random
import sys

flag = 0

def generate_clauses(f):
    lines = f.read().split('\n')
    nums = lines[0].split()
    m = int(nums[0])
    n = int(nums[1])
    lists = []
    for i in range(m):
        l = []
        for j in range(n):
            l.append(str(i + 1) + '|' + str(j + 1))
        lists.append(l)

    for l in lists:
        c = ""
        for literal in l:
            c += ('t' + literal)
        clauses.append(c)

    for l in lists:
        if len(l) <= 1:
            break
        c = ""
        for i in range(len(l)):
            tmp_str1 = 'f' + l[i]
            c += tmp_str1
            for j in range(i + 1, len(l)):
                tmp_str2 = 'f' + l[j]
                c += tmp_str2
                clauses.append(c)
                c = c[:len(c) - len(tmp_str2)]
            c = c[:len(c) - len(tmp_str1)]

    for line in lines[1:]:
        if len(line) == 0:
            continue
        line = line.split()
        a = int(line[0])
        b = int(line[1])
        if line[2] == 'E':
            for i in range(n):
                c = ""
                c += ('f' + str(a) + '|' + str(i + 1))
                c += ('f' + str(b) + '|' + str(i + 1))
                clauses.append(c)
        elif line[2] == 'F':
            for i in range(n):
                c1 = ""
                c2 = ""
                c1 += ('f' + str(a) + '|' + str(i + 1))
                c1 += ('t' + str(b) + '|' + str(i + 1))
                clauses.append(c1)
                c2 += ('t' + str(a) + '|' + str(i + 1))
                c2 += ('f' + str(b) + '|' + str(i + 1))
                clauses.append(c2)
        else:
            print "invalid input, program terminated."
            exit(1)

def get_literals(c):
    lits = []
    i = 0
    for j in range(len(c)):
        if j > 0 and (c[j] == 't' or c[j] == 'f'):
            lits.append(c[i: j])
            i = j
    lits.append(c[i:])
    return lits


def get_symbols(c): # returns a set a symbols
    lits = get_literals(c)
    symbols = set([])
    for lit in lits:
        symbols.add(lit[1:])
    return symbols

def get_all_symbols(clauses):
    all_symbols = set([])
    for clause in clauses:
        all_symbols.update(get_symbols(clause))
    return all_symbols

def generate_random_assignments(symbols):
    assignmnt = dict()
    for sym in symbols:
        ran = random.randint(0, 1)
        assignmnt[sym] = ran
    return assignmnt

def satisfy(c, model): # precondition: model_covers_all_symbols(c, model) returns true
    lits = get_literals(c)
    for lit in lits:
        sym = lit[1:]
        if lit[0] == 'f':
            value = 0
        else:
            value = 1
        if value == model[sym]:
            return True
    return False

def get_false_clauses(clauses, model):
    unsatisfied_clauses = []
    for c in clauses:
        if not satisfy(c, model):
            unsatisfied_clauses.append(c)
    return unsatisfied_clauses

def get_random_clause(unsatisfied_clauses):
    ran = random.randint(0, len(unsatisfied_clauses) - 1)
    c = unsatisfied_clauses[ran]
    return c

def flip_symbol(model, p, s):
    val = random.random()
    flag = 1
    if val > p:
        flag = 0
    if flag == 1:
        model[s] = 1 - model[s]


def model_covers_all_symbols(c, model):
    symbols = get_symbols(c)
    return set(model.keys()).issuperset(symbols)


def find_pure_symbol(symbols, clauses, model):
    ret = dict()
    lits_set = set([])
    for c in clauses:
        if model_covers_all_symbols(c, model) and satisfy(c, model):
            continue
        lits = get_literals(c)
        lits_set.update(lits)
    for sym in symbols:
        if ('t' + sym) in lits_set and ('f' + sym) in lits_set:
            continue
        if ('t' + sym) in lits_set:
            ret[sym] = 1
        elif ('f' + sym) in lits_set:
            ret[sym] = 0
    return ret

def is_false(lit, model):
    if (lit[0] == 't' and model[lit[1:]] == 0) or (lit[0] == 'f' and model[lit[1:]] == 1):
        return True
    return False

def find_unit_clause(clauses, model):
    ret = dict()
    new_model = dict()
    new_model.update(model)
    while 1:
        can_find = False
        for c in clauses:
            if model_covers_all_symbols(c, new_model) and satisfy(c, new_model):
                continue
            lits = get_literals(c)
            remove_list = []
            for lit in lits:
                if lit[1:] in new_model.keys() and is_false(lit, new_model):
                    remove_list.append(lit)
            if len(lits) - len(remove_list) == 1:
                can_find = True
                for r in remove_list:
                    lits.remove(r)
                unit_lit = lits[0]
                if unit_lit[0] == 't':
                    ret[unit_lit[1:]] = 1
                else:
                    ret[unit_lit[1:]] = 0
            new_model.update(ret)
        if not can_find:
            break
    return ret

def dpll(clauses, symbols, model):
    model_completed = True
    for c in clauses:
        if not model_covers_all_symbols(c, model):
            model_completed = False
        elif not satisfy(c, model):
            return False
    if model_completed:
        return True

    pure_symbols = find_pure_symbol(symbols, clauses, model)
    if len(pure_symbols.keys()) != 0:
        symbols_copy = symbols - set(pure_symbols.keys())
        pure_symbols.update(model)
        return dpll(clauses, symbols_copy, pure_symbols)

    unit_clauses = find_unit_clause(clauses, model)
    if len(unit_clauses.keys()) != 0:
        symbols_copy = symbols - set(pure_symbols.keys())
        unit_clauses.update(model)
        return dpll(clauses, symbols_copy, unit_clauses)

    next_sym = symbols.pop()
    rest_symbols1 = copy.deepcopy(symbols)
    rest_symbols2 = copy.deepcopy(symbols)
    model1 = copy.deepcopy(model)
    model2 = copy.deepcopy(model)
    model1[next_sym] = 0
    model2[next_sym] = 1
    return dpll(clauses, rest_symbols1, model1) or dpll(clauses, rest_symbols2, model2)


def dpll_satisfiable(clauses):
    all_symbols = get_all_symbols(clauses)
    model = dict()
    return dpll(clauses, all_symbols, model)

def walksat(clauses, p, max_flips): #clauses is a list
    all_symbols = get_all_symbols(clauses)
    model = generate_random_assignments(all_symbols) # a hash map
    for i in range(max_flips):
        false_clauses = get_false_clauses(clauses, model) # a list of false clauses
        if len(false_clauses) == 0:
            return model;
        r_clause = get_random_clause(false_clauses)
        symbols = get_symbols(r_clause)
        random_symbol = random.sample(symbols, 1)[0]
        flip_symbol(model, p, random_symbol)
    return None



f = open("input.txt", "r")
out = open('output.txt', 'w')
clauses = []
generate_clauses(f)
if len(clauses) == 0:
    print "Invalid input, program terminated."
    exit(1)

has_answer = dpll_satisfiable(clauses)
if has_answer:
    out.write("yes\n")

    model = walksat(clauses, 0.5, 100000)
    result = dict()
    for assgn in model.keys():
        if model[assgn] == 1:
            vals = assgn.split('|')
            result[vals[0]] = vals[1]

    for key in sorted(result.iterkeys()):
        out.write("%s %s\n" % (key, result[key]))
else:
    out.write("no\n")
#res = pl_resolution()
#if res:
#    print "Yes\n"
#else:
#    print "No\n"