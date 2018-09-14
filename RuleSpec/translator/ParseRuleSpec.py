import re
import lex
import yacc
import uig
import os.path
import logic

reserved = {
            'if':    'IF',
            'then':  'THEN',
            'else':  'ELSE',
            'endif': 'ENDIF',
            'or':   'OR',
            'and':  'AND',
            'not':  'NOT',
            'mod': 'MOD',
            'div': 'DIV'
    }

tokens = ['PLUS', 'MINUS', 'DIVIDE', 'TIMES', 'NUMBER', 'STRING', 'CONSTANT', 'COMPARISON_OPERATOR',
          'EQUALS', 'LPAREN', 'RPAREN'] + list(reserved.values())

t_PLUS = '\+'
t_MINUS = '-'
t_DIVIDE = '/'
t_TIMES = '\*'
t_COMPARISON_OPERATOR = '<=|>=|<>|>|<|=='
t_EQUALS = '='
t_LPAREN = '\('
t_RPAREN = '\)'
t_ignore = ' \t\n'


def t_COMMENT(t):
    """\#.*"""
    pass


def t_NUMBER(t):
    """[-+]?[0-9]*\.?[0-9]+"""
    return t


def t_STRING(t):
    """\"[A-Za-z0-9][A-Za-z0-9_]*\""""
    return t


def t_CONSTANT(t):
    """[A-Za-z][A-Za-z0-9]*\[[a-zA-z0-9]*\]|((?:[A-Za-z][A-Za-z0-9_]*))"""
    t.type = reserved.get(t.value, 'CONSTANT')
    return t


def t_error(t):
    print("illegal character {}".format(t))
    print("Illegal character '%s'" % t.value[0])
    t.lexer.skip(1)


precedence = (
    ('left', 'PLUS', 'MINUS'),
    ('left', 'TIMES', 'DIVIDE', 'MOD', 'DIV'),
)


lexer = lex.lex()


class Node:
    def __init__(self, type, children=None, leaf=None):
        self.type = type
        if children:
            self.children = children
        else:
            self.children = []
        self.leaf = leaf


def p_statements(p):
    """STATEMENTS : STATEMENT
                  | STATEMENT STATEMENTS"""
    statements = []
    for i in range(1, len(p)):
        statements.append(p[i])
    p[0] = Node("statements", statements)


def p_statement(p):
    """STATEMENT : EQUALITY
                 | IF_THEN_ELSE"""
    p[0] = p[1]


def p_equality(p):
    """EQUALITY : CONSTANT EQUALS EXPRESSION
                | CONSTANT EQUALS STRING"""
    p[0] = Node("equality", [p[1], p[3]], p[2])


def p_expression(p):
    """EXPRESSION : CONSTANT
                  | NUMBER
                  | EXPRESSION PLUS EXPRESSION
                  | EXPRESSION MINUS EXPRESSION
                  | EXPRESSION TIMES EXPRESSION
                  | EXPRESSION DIVIDE EXPRESSION
                  | EXPRESSION MOD EXPRESSION
                  | EXPRESSION DIV EXPRESSION
                  | LPAREN EXPRESSION RPAREN """
    if len(p) == 2:
        p[0] = p[1]
    elif len(p) == 4 and p[1] == '(':
        p[0] = Node("expression", [p[2]])
    else:
        p[0] = Node("expression", [p[1], p[3]], p[2])


def p_IF_THEN_ELSE(p):
    """IF_THEN_ELSE : IF CONDITION THEN STATEMENTS ENDIF
                    | IF CONDITION THEN STATEMENTS ELSE STATEMENTS ENDIF"""
    if len(p) == 6:
        p[0] = Node("if_then_else", [p[2], p[4]], [p[1], p[3], p[5]])
    elif len(p) == 8:
        p[0] = Node("if_then_else", [p[2], p[4], p[6]], [p[3], p[5], p[7]])


def p_condition(p):
    """CONDITION : LITERAL
                 | CONDITION AND CONDITION
                 | CONDITION OR CONDITION
                 | LPAREN CONDITION AND CONDITION RPAREN
                 | LPAREN CONDITION OR CONDITION RPAREN"""
    if p[1] == '(':
        i = 2
    else:
        i = 1
    literals = [p[i]]
    leafs = []
    if len(p[i:]) >= 3:
        if p[i+1] == 'or':
            leafs.append('or')
        else:
            leafs.append('and')
        literals.append(p[i+2])
    p[0] = Node("condition", literals, leafs)


def p_literal(p):
    """LITERAL : ATOMIC_FORMULA
               | NOT ATOMIC_FORMULA"""
    if len(p) == 2:
        p[0] = Node("literal", [p[1]])
    elif len(p) == 3:
        p[0] = Node("literal", [p[1]], p[2])


def p_atomic_formula(p):
    """ATOMIC_FORMULA : LPAREN CONSTANT RPAREN
                      | LPAREN CONSTANT COMPARISON_OPERATOR NUMBER RPAREN
                      | LPAREN CONSTANT COMPARISON_OPERATOR STRING RPAREN
                      | LPAREN CONSTANT COMPARISON_OPERATOR CONSTANT RPAREN"""
    if len(p) == 4:
        p[0] = Node("atomic_formula", [p[2]])
    elif len(p) == 6:
        p[0] = Node("atomic_formula", [p[2], p[4]], p[3])


def p_error(p):
    print(p)
    print("Syntax error in input!")


parser = yacc.yacc()


def print_ast(node):
    print("AST Node: {} {}".format(node, node.type))
    print("   Children:")
    for child in node.children:
        if isinstance(child, Node):
            print("      {} {}".format(child, child.type))
        else:
            print("      {} ".format(child))
    print("   Leaf    :  {}".format(node.leaf))
    for child in node.children:
        if type(child) is Node:
            print_ast(child)


global inputs, outputs, symbol_table
inputs = []
outputs = []


def ensure_constant(name, mode):
    global inputs, outputs
    if name[0:1].isupper():
        name = 's' + name
    name = re.sub("\]", ")", name, 1)
    name = re.sub("\[", "(", name, 1)
    if mode == 'input':
        if name not in inputs:
            inputs.append(name)
    elif mode == 'output':
        if name not in outputs:
            outputs.append(name)
    else:
        print("Invalid mode supplied to ensure_constant")
    return name


def print_ui():
    global inputs, outputs
    print("inputs={}".format(inputs))
    print("outputs={}".format(outputs))


def ast2epilog(ast):
    global inputs, outputs, symbol_table
    symbol_table = {}
    if ast.type == "statements":
        output = ''
        for statement in ast.children:
            output += '\n\n\n' + ast2epilog(statement)
        return output
    elif ast.type == "if_then_else":
        return translate_if_then_else(ast, [])
    elif ast.type == "equality":
        return translate_equality_ast(ast)
    else:
        print("Unrecognized AST Type")


global var_counter


var_counter = 0


def get_variable(constant=None):
    global var_counter, symbol_table
    if constant in symbol_table:
        return symbol_table[constant]
    elif constant:
        var_counter += 1
        symbol_table[constant] = 'X' + str(var_counter)
        return symbol_table[constant]
    else:
        var_counter += 1
        return 'X' + str(var_counter)


def lookup_symbol_table(constant):
    for key, value in symbol_table.items():
        if symbol_table[key] == constant:
            return key


def lookup_values(constants):
    global outputs
    if constants == set():
        return ''
    else:
        output_string = ''
        for constant in constants:
            constant_symbol = lookup_symbol_table(str(constant))
            if constant_symbol and constant_symbol not in outputs:
                output_string = write_output(output_string, 'value(' + constant_symbol +
                                             ',' + str(constant) + ')', ' & ')
        return output_string


def get_operand(child):
    if isinstance(child, Node) and child.type == 'expression':
        operand, output_string = translate_expression(child)
    elif child.isnumeric():
        operand = child
        output_string = ''
    else:
        child_constant = ensure_constant(child, 'input')
        operand = get_variable(child_constant)
        output_string = ''
    return operand, output_string


epilog_operator = {'+': 'plus', '-': 'minus', '*': 'times', '/': 'quotient', 'mod': 'mod', 'div': 'div'}


epilog_comparator = {'>': 'greater_than', '<': 'less_than', '>=': 'greater_than_equal_to',
                     '<=': 'less_than_equal_to', '==': 'same', '<>': 'distinct'}


def translate_expression(expression):
    if isinstance(expression, str):
        if is_number(expression) or is_string(expression):
            return expression, ''
        else:
            operand, output_string = get_operand(expression)
            return operand, output_string
    elif expression.leaf is None:
        return translate_expression(expression.children[0])
    else:
        operator = expression.leaf
        operand1, output_string1 = get_operand(expression.children[0])
        operand2, output_string2 = get_operand(expression.children[1])
        output_variable = get_variable()
        output_string = write_output(output_string1, output_string2, ' & ')
        output_string3 = epilog_operator[operator] + '(' + operand1 + ',' + operand2 + ',' + output_variable + ')'
        output_string = write_output(output_string, output_string3, ' & ')
        return output_variable, output_string


def translate_equality(ast):
    if isinstance(ast.children[1], str) and (is_number(ast.children[1]) or is_string(ast.children[1])):
        return translate_equality_assignment(ast)
    else:
        return translate_equality_expression(ast)


def translate_equality_ast(ast):
    antecedent, consequent = translate_equality(ast)
    if antecedent:
        return consequent + ' :- ' + antecedent
    else:
        return consequent


def translate_equality_assignment(ast):
    child_constant = ensure_constant(ast.children[0], 'input')
    return '', 'value(' + child_constant + ',' + ast.children[1] + ')'


def translate_equality_expression(ast):
    output_variable, output_string = translate_expression(ast.children[1])
    child_constant0 = ensure_constant(ast.children[0], 'output')
    output_variable0 = get_variable(child_constant0)
    output_string = write_output(output_string, 'same(' + output_variable + ',' + output_variable0 + ')', ' & ')
    return output_string, 'value(' + child_constant0 + ',' + output_variable0 + ')'


def is_string(s):
    if isinstance(s, str) and s[0] == '\"' and s[len(s) - 1] == '\"':
        return True
    else:
        return False


def is_number(s):
    try:
        float(s)
        return True
    except ValueError:
        return False


def translate_atomic_formula(atomic_formula):
    child_constant0 = ensure_constant(atomic_formula.children[0], 'input')
    if len(atomic_formula.children) == 1:
        output_string = 'value(' + child_constant0 + ',' + 'true' + ')'
        return output_string
    elif len(atomic_formula.children) == 2:
        output_string = ''
        if isinstance(atomic_formula.children[1], str):
            variable0 = get_variable(child_constant0)
            if is_number(atomic_formula.children[1]) or is_string(atomic_formula.children[1]):
                output_string = write_output(output_string, epilog_comparator[atomic_formula.leaf] + '(' + variable0 +
                                             ',' + atomic_formula.children[1] + ')', ' & ')
                return output_string
            else:
                child_constant1 = ensure_constant(atomic_formula.children[1], 'input')
                variable1 = get_variable(child_constant1)
                output_string = write_output(output_string, epilog_comparator[atomic_formula.leaf] +
                                             '(' + variable0 + ',' + variable1 + ')', ' & ')
                return output_string


def translate_literal(literal):
    if literal.leaf == 'not':
        return '~' + translate_atomic_formula(literal.children[0])
    else:
        output_string = translate_atomic_formula(literal.children[0])
        return output_string


def logical_connector(connector):
    if connector == 'and':
        return ' & '
    else:
        return ' | '


def translate_condition(condition):
    if len(condition.children) == 1:
        output_string = translate_literal(condition.children[0])
        return output_string
    else:
        if condition.type == 'literal':
            output_string = translate_literal(condition.children[0])
        else:
            output_string = translate_condition(condition.children[0])
        output_string += logical_connector(condition.leaf[0]) + translate_condition(condition.children[1])
        return output_string


def r2l(string):
    return re.sub("\"", 'xxx', string)


def l2r(string):
    return re.sub("xxx", '\"', string)


def translate_if_then_else_branch(statement, conditions):
    antecedent = ''
    for condition in conditions:
        polarity = condition[0]
        translated_condition = ''
        translated_condition = write_output(translated_condition, translate_condition(condition[1]), ' & ')
        if polarity == 'positive':
            translated_condition = '(' + translated_condition + ')'
        else:
            translated_condition = ' ~(' + translated_condition + ')'
        antecedent = write_output(antecedent, translated_condition, ' & ')
    equality_antecedent, equality_consequent = translate_equality(statement)
    if equality_antecedent:
        antecedent = write_output(antecedent, equality_antecedent, ' & ')
    antecedent_dnf = logic.to_dnf(r2l(antecedent))
    output_string = ''
    for arg in logic.disjuncts(antecedent_dnf):
        antecedent = lookup_values(logic.constant_symbols(arg))
        antecedent = l2r(write_output(antecedent, ("%s" % arg), ' & '))
        output_string += equality_consequent + ' :- ' + antecedent + '\n'
    return output_string


def flatten_statements(statements):
    statement_tree = []
    for statement in statements.children:
        if statement.type == "statements":
            statement_tree.extend(flatten_statements(statement))
        elif statement.type == "equality" or statement.type == "if_then_else":
            statement_tree.append(statement)
        else:
            print("error found in statements")
    return statement_tree


def translate_if_then_else(ast, conditions):
    output_string = ''
    conditions.append(['positive', ast.children[0]])
    for statement in flatten_statements(ast.children[1]):
        if statement.type == "if_then_else":
            output_string += translate_if_then_else(statement, conditions)
        else:
            output_string += translate_if_then_else_branch(statement, conditions)
    conditions.pop()
    if len(ast.children) > 2:
        conditions.append(['negative', ast.children[0]])
        for statement in flatten_statements(ast.children[2]):
            if statement.type == "if_then_else":
                output_string += translate_if_then_else(statement, conditions)
            else:
                output_string += \
                    translate_if_then_else_branch(statement, conditions)
    return output_string


def write_output(output_string, input_string, connective):
    if output_string == '':
        output_string = input_string
    elif input_string != '':
        output_string = output_string + connective + input_string
    return output_string


def main():
    rule_library = ''
    input_file = os.path.join('..', 'rules', 'tax_calc.rs')
    output_file = os.path.join('..', 'rules', 'tax_calc.epilog')
    with open(input_file, 'r') as f:
        input_rules = f.read()
    lexer.input(input_rules)
    parse_output = parser.parse(input_rules, lexer=lexer)
    translation_output = ast2epilog(parse_output)
    rule_library += translation_output
    print(translation_output)
    global inputs, outputs
    with open(output_file, 'w') as f:
        f.write("minus(X,Y,Z) :- times(Y,-1,Y1) &amp;  plus(X,Y1,Z)\n")
        f.write("div(X,Y,Z) :- quotient(X,Y,Y1) &amp; floor(Y1,Z)\n")
        f.write("mod(X,Y,Z) :- div(X,Y,Y1) &amp;  times(Y1,Y,Y2) &amp;  minus(X,Y2,Z)\n")
        f.write("less_than(X,Y) :- ~ max(X,Y,X) \n")
        f.write("greater_than(X,Y) :- ~ min(X,Y,X) \n")
        f.write(translation_output)
        for input_item in inputs:
            if input_item not in outputs:
                f.write('input(' + input_item + ')' + '\n')
        for output in outputs:
            f.write('output(' + output + ')' + '\n')

    rule_library += translation_output
#    uig.output_worksheet(inputs, outputs, rule_library)


if __name__ == "__main__":
    main()
