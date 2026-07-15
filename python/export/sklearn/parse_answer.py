from ResultObj import ResultObj
from utils import list_from_string


def read_answer_file(filename: str)-> str:
    """Read a file and return the string of its content."""
    with open(filename, 'r') as f:
        return f.read()


def read_answer(answer: str)-> ResultObj:
    """Create the `ResultObj` from the answer of OCaml program.
    The answer must follow this form :
    ```
    axp : [1, 3]
    cxp : [1, 2, 3]
    axp : [2]
    ```
    """

    # result of the function, list of ResultObj
    r = []

    # temp lists containing axps and cxps of the current vector
    axps = []
    cxps = []


    def register_and_clear():
        nonlocal axps, cxps
        r.append(ResultObj(axps, cxps))
        axps = []
        cxps = []

    lines = answer.split('\n')
    lines = list(filter(lambda x: x!='', lines)) # filter empty lines

    for i, line in enumerate(lines):
        l = [ e.strip() for e in line.split(':') ]
        if l[0].lower() == "axp":
            try:
                l = list_from_string(l[1])
                axps.append(l)
            except:
                print(f"warning : explanation n°{i} is not correctly written. It is not read.")
        elif l[0].lower() == "cxp":
            try:
                l = list_from_string(l[1])
                cxps.append(l)
            except:
                print(f"warning : explanation n°{i} is not correctly written. It is not read.")
        elif l[0] == ";":
            if (axps or cxps): register_and_clear()
        else:
            print(f"warning : explanation n°{i} is neither axp nor cxp. It is not read")

    if axps or cxps:
        register_and_clear()

    return r
