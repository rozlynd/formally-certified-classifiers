import numpy as np
from sklearn import tree
from sklearn.tree import _tree

from utils import flatten_str_list



def export_tree(dt: tree.DecisionTreeClassifier)-> str:
    """
    Export a `DecisionTree` from `sklearn` module to a string format.

    The generated string has this format :
    - each line represents a vertex (that can be a leaf or a node)
    - a leaf is represented like this :
        `L(value)`
    - a node is reprensented like this :
        `N(feature_index, threshold, child_left_index, child_right_index)`
    
    Example :
    The model is the iris dataset from `sklearn.datasets` (function `load_iris`)
     (representation made by `export_text` function in module `sklearn.tree`) :
        
    ```
    |--- petal width (cm) <= 0.80
    |   |--- class: 0
    |--- petal width (cm) >  0.80
    |   |--- petal width (cm) <= 1.75
    |   |   |--- class: 1
    |   |--- petal width (cm) >  1.75
    |   |   |--- class: 2
    ```

    This function should generate this representation :

    ```
    T(
        N(0, 0.8, 1, 2),
         L(0),
         N(1, 1.75, 3, 4),
          L(1),
          L(2)
    )
    ```

    """

    t = dt.tree_
    r = []
    def f(r:list[str], node: int, prefix: str = ""):
        """
        Recursive function writing in the string `r` the informations about the node `node`.\n
        `node` is the index of the current node.
        `prefix` is the string to write before the node informations in r, 
        it is used to put identations for the file to be more readable.
        """

        ## exhaustion : node/leaf
        if t.feature[node] != _tree.TREE_UNDEFINED:
            ## node case

            left_child_index = t.children_left[node]
            right_child_index = t.children_right[node]

            line = (
                prefix + "N(" +
                str(t.feature[node]) + ", " +
                t.threshold[node].hex() + ", " + # use the hex representation of floats to avoid approximations
                str(left_child_index) + ", " +
                str(right_child_index) +
                "),"
            )

            r.append(line)

            f(r, left_child_index, prefix + " ")
            f(r, right_child_index, prefix + " ")
        else:
            ## leaf case

            if t.n_outputs == 1:
                value = t.value[node][0]
            else:
                value = t.value[node].T[0]
            class_name = np.argmax(value)

            line = prefix + "L(" + str(class_name) + "),"
            r.append(line)
    
    r.append("T(")

    ## call on the root node (index 0)
    f(r, 0, "\t")

    ## remove the last ','
    if r[-1][-1] == ",":
        r[-1] = r[-1][:-1]
    
    r.append(")")

    return flatten_str_list(r)














# def comment_node_info(node_index: int, left_child_index: int = None, right_child_index: int = None):
#     comment =  "(* " + \
#                 "node_index : " + str(node_index)
#     if left_child_index != None and right_child_index != None:
                
#         comment += " ; left_child_index : " + str(left_child_index) + \
#                     " ; right_child_index : " + str(right_child_index) + \
#                     " *)"
#     return comment + " *)"