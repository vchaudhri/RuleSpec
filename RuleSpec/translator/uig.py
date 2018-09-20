import os.path

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
    "    <script src=\"../javascript/epilog.js\"></script> \n " \
    "    <script src=\"../javascript/worksheets.js\"> </script> \n " \
    "  </head> \n  " \
    "  <body onload=\"initialize() ; queryOutputs ()\" style=\"width: 100%; overflow: auto; "\
    "    margin: 0px; box-sizing: border-box;\"> \n"


footer = " </body> \n " \
    "</html> \n "


def write_library(f, rule_library):
    f.write('<pre id= "lambda\" style=\"display:none;\" type="text/hrf"></pre >\n')
    f.write('<pre id=\"library\" style=\"display:none;\" type=\"text/hrf\">')
    f.write('subtract(X,Y,Z) :- times(Y,-1,Y1) &amp;  plus(X,Y1,Z)\n')
    f.write('div(X,Y,Z) :- quotient(X,Y,Y1) &amp; floor(Y1,Z)\n')
    f.write('mod(X,Y,Z) :- div(X,Y,Y1) &amp;  times(Y1,Y,Y2) &amp;  subtract(X,Y2,Z)\n')
    f.write('less_than(X,Y) :- ~ max(X,Y,X) \n')
    f.write('greater_than(X,Y) :- max (X,Y,X) \n')
    f.write(rule_library)


def write_ui_rules (f, inputs, outputs):
    f.write("%%ui scaffolding%% \n")
    for input_item in inputs:
        if input_item not in outputs:
            f.write('input(' + input_item + ')' + '\n')
    for output in outputs:
        f.write('output(' + output + ')' + '\n')
    y_coord = 50
    for input_item in inputs:
        f.write('select(' + input_item + ',X) ==> ' + input_item + '(X) \n')
        f.write('select(' + input_item + ',X)' + ' & ' + input_item + '(Y) ==> ~' + input_item + '(Y) \n')
        f.write('value(' + input_item + ',X) :- ' + input_item + '(X) \n')
        f.write('attribute(text(' + input_item + ',yoffset,' + str(y_coord) +
                ')) :- input(' + input_item + ') \n')
        f.write('insertrow(input_table(' + input_item + ',X)) ==> ' + input_item + '(X) \n')
        f.write('deleterow(input_table(' + input_item + ',X)) ==> ~' + input_item + '(X) \n')
        f.write('updaterow(input_table(' + input_item + ',X), input_table(' + input_item + ',Y)) ==> '
                '~' + input_item + '(X) & ' + input_item + '(Y) \n')
        y_coord += 20
    for output_item in outputs:
        f.write('value(' + output_item + ',X) :- ' + output_item + '(X) \n')
    f.write('style(X,\"display\",\"none\") :- input(X) & ~current(X) \n')
    f.write('style(X,\"display\",\"\") :- input(X) & current(X) \n')
    f.write('style(text(X),\"display\",\"none\") :- input(X) & ~current(X) \n')
    f.write('style(text(X),\"display\",\"\") :- input(X) & current(X) \n')
    f.write('attribute(X, xref,Xs) :- input(X) & stringify(text(X), Xs) \n')
    f.write('attribute(X, yref,Xs) :- input(X) & stringify(text(X), Xs) \n')
    f.write('attribute(text(X), xoffset, 100) :- input(X) \n')
    f.write('attribute(X, xoffset, right) :- input(X) \n')
    f.write('attribute(X, yoffset, center) :- input(X) \n')
    f.write('innerhtml(text(X), Str) :- input(X) & stringify(X,Xs) & stringappend(Xs, \": \", Str)\n')
    f.write('output_table(X,Y) :- output(X) & value(X,Y) \n')
    f.write('input_table(X,Y) :- input(X) & value(X,Y) \n')
    f.write('attribute(output_table, yoffset, 240) \n')
    f.write('%%end ui scaffolding%% \n')
    f.write('</pre>\n')


def write_ui_widgets (f, inputs):
    for input_item in inputs:
        f.write('<input type=\"text\" onchange=\"modtext(this); queryOutputs();\" id=\"' + input_item +
                '\" data-x=\"NaN\" data-y=\"NaN\" widget=\"objectfield\" style=\"border: 1px solid lightgrey; '
                'outline: 0px; box-sizing: border-box; margin: 0px; position: absolute; display: none; '
                'border-radius: 0px; -moz-border-radius: 0px; -webkit-border-radius: 0px;\" xoffset=\"right\" '
                'yoffset=\"center\" class=\"\" positioned=\"true\" xref=\"\" yref=\"\"> \n\n')
        f.write('<div spellcheck=\"false\" autocomplete=\"false\" id=\"text(' + input_item +
                ')\" data-x=\"100\" data-y=\"50\" widget=\"div\" style=\"background-color: white; box-sizing: '
                'border-box; flex-direction: column; text-align: left; justify-content: flex-start; '
                'overflow: auto; margin: 0px; position: absolute; display: none; '
                'border-radius: 0px; -moz-border-radius: 0px; -webkit-border-radius: 0px;\"  xref=\"\" yref=\"\" '
                'class=\"\" positioned=\"true\"></div>\n')
    f.write('<table border=\"1\" cellspacing=\"0\" arity=\"2\" class=\"data-table\" id=\"output_table\" '
            'editable-row-color=\"lightblue\" header-background=\"#333\" header-color=\"#EEE\" '
            'header-alignment=\"center\" widget=\"table\" data-x=\"35.7735\" data-y=\"324.342375\" '
            'style=\"width: 200px; background-color: white; transform: translate(35.7735px, 324.342px); '
            'position: absolute; border-radius: 0px; -moz-border-radius: 0px; -webkit-border-radius: 0px;\" '
            'xoffset=\"50\" yoffset=\"\" xref=\"\" yref=\"\" positioned=\"true\"><caption><strong>Output</strong><'
            '/caption><thead><tr style=\"font-weight: bold; background-color: rgb(51, 51, 51); '
            'color: rgb(238, 238, 238); text-align: center;\"><td type=\"object\">Name</td><td '
            'type=\"object\">Value</td></tr></thead><tbody></tbody></table> \n\n')
    f.write('<table onclick=\"queryOutputs();\" border=\"1\" cellspacing=\"0\" arity=\"2\" class=\"data-table\" '
            'editable=\"true\" id=\"input_table\" editable-row-color=\"lightblue\" header-background=\"#333\" '
            'header-color=\"#EEE\" header-alignment=\"center\" widget=\"table\" data-x=\"335.77349853515625\" '
            'data-y=\"324.3423767089844\" style=\"width: 200px; background-color: white; transform: '
            'translate(335.773px, 324.342px); position: absolute; border-radius: 0px; -moz-border-radius: '
            '0px; -webkit-border-radius: 0px;\" xoffset=\"300\" yoffset=\"0\" xref=\"output_table\" '
            'yref=\"output_table\" positioned=\"true\"><caption><strong>Inputs</strong></caption><thead>'
            '<tr style=\"font-weight: bold; background-color: rgb(51, 51, 51); color: rgb(238, 238, 238); '
            'text-align: center;\"><td type=\"object\">Name</td><td type=\"object\">Value</td><td></td>'
            '<td></td></tr></thead><tfoot><tr style=\"text-align: center; color: rgb(51, 51, 51); '
            'background-color: rgb(238, 238, 238); padding-top: 10px;\"><td colspan=\"4\"><strong '
            'onclick=\"addtablerow(this.parentNode)\" style=\"cursor: pointer;\">&#10010; '
            'Add row</strong></td></tr></tfoot><tbody></tbody></table> \n\n')


def output_worksheet(inputs, outputs, rule_library):
    ws = r'worksheet.html'
    with open(ws, 'w+') as f:
        f.write(header)
        write_library(f, rule_library)
        write_ui_rules(f, inputs, outputs)
        write_ui_widgets(f, inputs)
        f.write(footer)
