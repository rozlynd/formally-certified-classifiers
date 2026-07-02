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

    axps = []
    cxps = []

    lines = answer.split('\n')
    lines = list(filter(lambda x: x!='', lines)) # filter empty lines

    for i, line in enumerate(lines) :
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
        else:
            print(f"warning : explanation n°{i} is neither axp nor cxp. It is not read")

    return ResultObj(axps, cxps)
