import re
import uig
from pathlib import Path

rule_spec = dict()
rule_spec[1] = "C[1]=50"
rule_spec[2] = 'P[n]=P[nm1]+p[n]'
rule_spec[3] = 'a1=(5000 / 52 * (code - 1) D 500) + ((((code - 1) M 500 + 1) * 10 + 9) / 52)'
rule_spec[4] = "if (code = 0) " \
               "a1 = 0       " \
               "else  " \
               "a1  = (5000 /52 * (code-1) div 500) + " \
               "(((code-1) mod 500 + 1) * 10 + 9) / 52 " \
               "endif"

epilog_operator = {'+': 'plus', '-': 'subtract', '*': 'times', '/': 'quotient', 'M': 'mod', 'D': 'div'}

def greater_precedence(op1, op2):
    precedences = {'+': 0, '-': 0, '*': 1, '/': 1, 'D': 2, 'M': 2}
    return precedences[op1] >= precedences[op2]

global constants
global inputs
global outputs
global rule_library

constants = []
inputs = []
outputs = []
rule_library = ""

global var_counter
var_counter = 0


def get_variable():
    global var_counter
    var_counter += 1
    return 'X' + str(var_counter)


def peek(stack):
    return stack[-1] if stack else None


def apply_operator(operator_stack, output_queue, output_string, symbol_table):
    if (output_string != ""):
        output_string += "  &amp; "
    output_string += ' ' + epilog_operator[operator_stack.pop()] + '('
    operand2 = output_queue.pop()
    operand1 = output_queue.pop()
    result_variable = get_variable()
    output_string += operand1 + ","
    output_string += operand2 + ',' + str(result_variable) + ')'
    output_queue.append(result_variable)
    return output_string





def ensure_constant(name):
    if name[0:1].isupper():
        name = 's' + name
    name = re.sub("\]", ")", name, 1)
    name = re.sub("\[", "(", name, 1)
    return name


def parse_expression(expression, symbol_table):
    global inputs
    tokens = re.findall("\(|\)|=|\+|-|\*|/|D|[a-z|A-Z|0-9|\[|\]]*", expression)
    tokens = list(filter(None, tokens))
    output_string = ""
    output_queue = []
    operator_stack = []
    for token in tokens:
        if token.isnumeric():
            output_queue.append(token)
        elif token == '(':
            operator_stack.append(token)
        elif token == ')':
            top = peek(operator_stack)
            while top is not None and top != '(':
                output_string = apply_operator(operator_stack, output_queue, output_string, symbol_table)
                top = peek(operator_stack)
            operator_stack.pop()  # Discard the '('
        elif token in '+-/*MD':
            # Operator
            top = peek(operator_stack)
            while top is not None and top not in "()" and greater_precedence(top, token):
                output_string = apply_operator(operator_stack, output_queue, output_string, symbol_table)
                top = peek(operator_stack)
            operator_stack.append(token)
        elif token in symbol_table:  # Constant
            output_queue.append(symbol_table[token])
        else:
            symbol_table[token] = get_variable()
            output_queue.append(symbol_table[token])
            inputs.append(ensure_constant(token))
            if (output_string != ""):
                output_string += "  &amp; "
            output_string += 'value({},{})'.format(ensure_constant(token), symbol_table[token])
    while peek(operator_stack) is not None:
        output_string = apply_operator(operator_stack, output_queue, output_string, symbol_table)
    return output_string


def parse_equality_expression(operand1, operand2):
    global outputs
    global rule_library
    symbol_table = {}
    parsed_expression = parse_expression(operand2, symbol_table)
    outputs.append(ensure_constant(operand1))
    print("value({},{}) :- {}".format(operand1, 'X' + str(var_counter), parsed_expression))
    rule_library += "value({0},X{1}) :- {2}\n".format(ensure_constant(operand1), str(var_counter),
                                                      parsed_expression)


def parse_equality(expression):
    global rule_library
    operand1 = expression[0:re.search("=", expression).start()]
    operand2 = expression[re.search("=", expression).end():]
    if operand2.isnumeric():
        print("value({},{})".format(ensure_constant(operand1), operand2))
        constants.append(ensure_constant(operand1))
        rule_library += "value(" + ensure_constant(operand1) + ',' + operand2 + ')' + '\n'
    else:
        parse_equality_expression(operand1, operand2)

def main():
    global constants, inputs, outputs, rule_library
    for i in range(1, 4):
        print("\n\nInput: \n{} \nOutput:".format(rule_spec[i]))
        parse_equality(rule_spec[i])
        print("\n constants: {} \n inputs: {} \n outputs: {} \n rule library: {} \n". \
              format(constants, inputs, outputs, rule_library))
        uig.output_worksheet(constants,inputs,outputs,rule_library)


if __name__ == "__main__":
    main()
