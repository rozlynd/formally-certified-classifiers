from sklearn import tree
import subprocess

from export_sklearn_data.export_tree import export_tree
from export_sklearn_data.export_vector import export_vector
from export_sklearn_data.export_features import export_features
from utils import write_str_in_file
from parse_answer import read_answer_file, read_answer


def logger(text: str, verbose: bool = True):
    if verbose: print(text)

def explain(dt: tree.DecisionTreeClassifier, v: list, data_filename: str ="data.txt", answer_filename = "ocaml_answer.txt", verbose: bool = False):
    """
    Explain a decision by calling OCaml program.\n
    Return a `ResultObj` containing the explanation(s) of the classification of `v` by the decision tree `dt`.
    
    Parameters
    ----------
    dt: tree.DecisionTreeClassifier
        the decision tree classifier
    
    v: list
        the classified vector
    
    data_filename: str
        name of the file where we write infos to communicate to OCaml program.
    
    answer_filename: str
        name where the OCaml program will write the explanation(s).
    
    verbose: bool
        is the execution of this function verbose ?
    """

    def log(s: str):
        logger(s, verbose)

    ## write features, tree and vector in a file nammed `data_filename`
    log("begin export...")
    text_features = export_features(v)
    text_tree = export_tree(dt)
    text_vector = export_vector(v)
    text = text_features + "\n\n" + text_tree + "\n\n" + text_vector + "\n\n"
    write_str_in_file(data_filename, text)
    log("end export.\n")


    ## run ocaml code

    log("begin running ocaml explanation...")

    verification_prog_path = "../../ocaml/_build/default/bin"
    command = f"""./{verification_prog_path}/main.exe -ac {data_filename} {answer_filename}"""

    ## run the command line in a shell, and capture the output
    res = subprocess.run(command, check=True, capture_output=True, shell=True, executable="/bin/bash")
    log("end running ocaml explanation.")
    
    # res_str = str(res.stdout, "utf-8") # translate bytes into string
    # log("output :" + res_str)

    ## parse ocaml answer file
    answer = read_answer_file(answer_filename)

    ## create the ResultObj and return it
    return read_answer(answer)

