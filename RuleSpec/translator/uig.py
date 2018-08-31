header = "<html> \n"  \
"<head> \n " \
"   <meta http-equiv=\"content-type\" content=\"text/html; charset=UTF-8\"> \n" \
"  <title>UK Payroll Taxes</title> \n " \
"    <meta charset=\"UTF-8\"> \n "\
"    <style class=\"worksheet\"> \n "\
"    [type=\'widget\'] > * \n "\
"    { \n "   \
"      min-height: 2px; \n "  \
"    } \n "  \
"    </style> \n " \
"    <script src=\"http://worksheets.stanford.edu/epilog/javascript/epilog.js\"></script> \n " \
"    <script src=\"http://worksheets.stanford.edu/javascript/worksheets.js\"> </script> \n " \
"  </head> \n  " \
"  <body onload=\"initialize()\" style=\"width: 100%; overflow: auto; margin: 0px; box-sizing: border-box;\"> \n"\
"    <pre id=\"lambda\" autostorage=\"true\" style=\"display:none;\" type=\"text/hrf\"> </pre> \n "\


footer = " </body> \n " \
"</html> \n "

library_header =    "<pre id=\"library\" style=\"display:none;\" type=\"text/hrf\">"

library_footer = "</pre>"

def write_constant(f,constant) :
    f.write("<br><div><p>Given constant: {}</p></div><br>".format(constant))
    f.write("<input onchange=\"modtext(this)\"  id=\"{}\" type=\"text\"><br><br>".format(constant))

def accept_input(f,input) :
    f.write("<br><div><p>Please input: {}</p></div>".format(input))
    f.write("<input onchange=\"modtext(this)\"  id=\"{}\" type=\"text\"><br><br>".format(input))

def print_output(f,output) :
    f.write("<br><div><p>Computed Output: {}</p></div>".format(output))
    f.write("<input onchange=\"modtext(this)\"  id=\"{}\" type=\"text\"><br><br>".format(output))

def write_library (f,rule_library) :
    f.write(library_header)
    f.write("subtract(X,Y,Z) :- times(Y,-1,Y1) &amp;  plus(X,Y1,Z)\n")
    f.write("div(X,Y,Z) :- quotient(X,Y,Y1) &amp; floor(Y1,Z)\n")
    f.write("mod(X,Y,Z) :- div(X,Y,Y1) &amp;  times(Y1,Y,Y2) &amp;  subtract(X,Y2,Z)\n")
    f.write(rule_library)
    f.write(library_footer)

def output_worksheet(inputs,outputs,rule_library):
    ws = r'worksheet.html'
    with open(ws, 'w+') as f:
        f.write(header)
        write_library(f,rule_library)
        if inputs != []:
            for input in inputs:
                accept_input(f,input)
        if outputs != []:
            for output in outputs:
                print_output(f,output)
        f.write(footer)