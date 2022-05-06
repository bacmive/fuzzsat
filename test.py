import random
import os
import re
import string
import tempfile
import subprocess
from pprint import pprint
from shutil import copy2

from ub import do_ub

FOLLOW_UP_TESTS = 'follow-up-tests'
SS_UU = 'SAT->SAT\nUNSAT->UNSAT\n'
SS_UUNKOWN = 'SAT->SAT\nUNSAT->UNKNOWN\n'
SUNKNOWN_UU = 'SAT->UNKNOWN\nUNSAT->UNSAT\n'

def swap_clauses(formula):
    copy = list(formula)
    random.shuffle(copy)

    return copy

def swap_literals(formula):
    result = []

    for clause in formula:
        copy = list(clause)

        del copy[-1]
        random.shuffle(copy)
        copy.append(0)

        result.append(copy)

    return result

def add_clauses(no_of_vars, no_of_clauses, formula):
    result = []

    for clause in formula:
        copy = list(clause)
        result.append(copy)

    no_of_new_clauses = random.randint(0, no_of_clauses)

    for i in range(0, no_of_new_clauses):
        new_clause = []

        # Generate clause of size between 1 to 10
        for j in range(0, random.randint(1, 10)):
            new_clause.append(random.randint(1, no_of_vars))

        new_clause.append(0)
        result.append(new_clause)

    return result, no_of_new_clauses

def delete_clauses(no_of_clauses, formula):
    no_of_deleted_clauses = random.randint(0, no_of_clauses)

    result = list(formula)[0:no_of_clauses - no_of_deleted_clauses]

    return result, no_of_deleted_clauses


def transform(formula, no_of_clauses, no_of_vars):
    # Apply a set of transformations based on these rules:
    # 0 - 4 Swap clauses (1)
    # 5 - 9 Swap literals inside a clause (2)
    # 10 - 14 Add clauses (3)
    # 15 - 19 Remove Clauses (4)
    # 20 - 24 (1+2)
    # 25 - 29 (1+3)
    # 30 - 34 (1+4)
    # 35 - 39 (2+3)
    # 40 - 44 (1+2+3)
    # 45 - 49 (1+2+4)

    # result is of the form: [(formula, no_of_clauses, sat_string)]
    result = []

    for i in range(0, 1):
        new_formula = (swap_clauses(formula), no_of_clauses, SS_UU)

        result.append(new_formula)

    for i in range(5, 6):
        new_formula = (swap_literals(formula), no_of_clauses, SS_UU)

        result.append(new_formula)

    for i in range(10, 11):
        new_formula, no_of_added_clauses = add_clauses(no_of_vars, no_of_clauses, formula)

        result.append((new_formula, no_of_added_clauses + no_of_clauses, SUNKNOWN_UU))

    for i in range(15, 16):
        new_formula, no_of_deleted_clauses = delete_clauses(no_of_clauses, formula)

        result.append((new_formula, no_of_clauses - no_of_deleted_clauses, SS_UUNKOWN))

    return result

def do_func(sut_path, inputs_path, seed):
    if seed is not None:
        random.seed(seed)
    else:
        random.seed()

    for x in range(1, 2):
        with open(os.path.join(inputs_path, str(x).zfill(2) + '.cnf')) as formula:
            first_line = formula.readline()

            p, cnf, no_of_vars, no_of_clauses = first_line.strip().split()

            clauses = []

            for line in formula:
                clauses.append(line.split())

        pprint(clauses)
        transformations = transform(clauses, int(no_of_clauses), int(no_of_vars))
        pprint("after transformations: ")
        pprint(transformations)


 #-----------------------------------do ub---------------------------------------#


SAVED_INPUTS_PATH = "fuzzed-tests/"
saved_inputs_id = 0

REGEXES = {
    "INTMIN_NEGATED_REGEX": re.compile('^.*runtime.+negation'),
    "NULLPOINTER_REGEX": re.compile('^.*runtime.+null pointer'),
    "SHIFT_ERROR_REGEX": re.compile('^.*runtime.+shift'),
    "USE_AFTER_FREE_REGEX": re.compile('^==.*AddressSanitizer: heap-use-after-free'),
    "HEAP_BUFFER_OVERFLOW_REGEX": re.compile('^==.*AddressSanitizer: heap-buffer-overflow'),
    "STACK_BUFFER_OVERFLOW_REGEX": re.compile('^==.*AddressSanitizer: stack-buffer-overflow'),
    "SIGNED_INTEGER_OVERFLOW_REGEX": re.compile('^.*runtime.+signed integer')
}

INTERSTING_CNFS = ["p cnf 0 0",
                   "p cnf 10 20\n!\"#$%&'()*+,-./:;<=>?@[\]^_`{|}~",
                   "p cnf 10 20\n\n\n0123456789abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ!\"#$%&'()*+,-./:;<=>?@[\]^_`{|}~ 	\n0\n00123456789abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ!\"#$%&'()*+,-./:;<=>?@[\]^_`{|}~ 	\n",
                   "p cnf 10 20\n\n\n01234567890123456789"]

DIGITS_NO_ZERO = string.digits.replace("0", "")

def do_ub(sut_path, inputs_path, seed):
    if seed is not None:
        random.seed(seed)
    else:
        random.seed()

    i = 0

    while True:
        if i < len(INTERSTING_CNFS):
            cnf = INTERSTING_CNFS[i]
            print("Sending interesting cnf")
        else:
            if i % 2 == 0:
                print("Sending input")
                cnf = create_input()
            else:
                print("Sending garbage")
                cnf = create_garbage()

        input_file = make_cnf_file(cnf)

        sut_output = run_sut(input_file, sut_path)

        if sut_output is not None:
            ubs = check_ub(sut_output)

            if ubs > 0:
                save_input(sut_path, input_file)

        input_file.close()

        i += 1

def create_input():
    number_of_formulas = 100000
    NUMBER_OF_LITERALS = 999
    formulas_width = 10

    cnf = "p cnf " + str(NUMBER_OF_LITERALS) + " " + str(number_of_formulas) + "\n999 0\n"
    for i in range(0, number_of_formulas):
        for j in range(0, formulas_width):
            cnf += ["", "-"][int(random.random() * 1)]
            num_width = random.randint(1, 3)
            for k in range(0, num_width):
                cnf += DIGITS_NO_ZERO[int(random.random() * 9)]
            cnf += " "
        cnf += "0\n"

    return cnf

def create_garbage():
    # nums_of_forms = random.randint(1, 20)
    # nums_of_vars = random.randint(1, 10)
    # cnf = "p cnf " + str(nums_of_forms) + " " + str(nums_of_vars)
    # cnf += " \n"
    cnf = "p cnf 10 20\n"

    while True:
        choice = random.randint(0, 5)
        if choice == 0:
            if len(cnf) >= 20:
                break
        elif choice == 1:
            cnf += string.punctuation
        elif choice == 2:
            cnf += string.printable
        elif choice == 3:
            cnf += string.digits
        elif choice == 4:
            cnf += '0'
        elif choice == 5:
            cnf += '\n'

    return cnf

def make_cnf_file(cnf):
    input_file = tempfile.NamedTemporaryFile(mode='w')
    input_file.write(cnf)
    input_file.flush()
    return input_file

def run_sut(input_file, sut_path):
    result = subprocess.Popen(["./runsat.sh", input_file.name], stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                              cwd=sut_path)
    
    try:
        sut_output, sut_error = result.communicate(timeout=10)
    except subprocess.TimeoutExpired:
        result.kill()
        print("TIMEOUT")
        return None

    sut_output_printable = sut_output.decode('ascii').split('\n')

    for line in sut_output_printable:
        print(line)

    return sut_error
    

def check_ub(sut_error):
    if sut_error == None:
        return 1
    
    ubs = 0
    for line in sut_error.decode('ascii').split('\n'):
        for key, value in REGEXES.items():
            if value.match(line):
                print(line)
                ubs += 1

    return ubs

def save_input(sut_path, temp_file):
    global saved_inputs_id

    os.makedirs(os.path.join(sut_path, SAVED_INPUTS_PATH), exist_ok=True)

    output_file = open(os.path.join(sut_path, SAVED_INPUTS_PATH, "interesting_input{}.txt".format(saved_inputs_id)),
                       'w+')

    copy2(temp_file.name, output_file.name)

    saved_inputs_id = (saved_inputs_id + 1) % 20

if __name__ == "__main__":
    # do_func("./suts/solver1", "./inputs", None)
    do_ub("./suts/solver1/", None, None)