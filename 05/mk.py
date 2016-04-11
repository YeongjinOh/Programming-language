#!/usr/bin/env python3

import sys

DELIMITER_PROBLEM = '(*=========== 3141592 ===========*)'
DELIMITER_CHECK = '(*-- Check --*)'

PREAMBLE_PROBLEM = 'Require Export D.\n\n'
def PREAMBLE_CHECK(i):
    return 'Require Import P%02d.\n\n' % i

def read_file(filename):
    with open(filename, 'r') as f:
        return f.read()

def write_file(filename, content):
    with open(filename, 'w') as f:
        return f.write(content)

if __name__ == '__main__':
    filename = sys.argv[1]
    content = read_file(filename)
    problems = content.split(DELIMITER_PROBLEM)

    write_file('D.v', problems[0])

    for i in range(1, len(problems)):
        problem_and_checks = problems[i].split(DELIMITER_CHECK)
        write_file('P%02d.v' % i, PREAMBLE_PROBLEM + problem_and_checks[0])
        for j in range(1, len(problem_and_checks)):
            write_file('E%02d_%02d.v' % (i, j), PREAMBLE_CHECK(i) + problem_and_checks[j])
