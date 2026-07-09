from sklearn import tree
from sklearn.tree import _tree
from random import uniform, random
from math import inf


def choose_vector(constraints: list[tuple[float,float]])-> list[float]:
    """Create a vector following given constraints."""
    v = [ 0. for i in range(len(constraints)) ]
    for i, (left_bound, right_bound) in enumerate(constraints):
        assert left_bound <= right_bound
        
        if left_bound == -inf and right_bound == inf:
            e = random()
        elif left_bound == -inf:
            e = uniform(right_bound-1, right_bound)
        elif right_bound == inf:
            e = uniform(left_bound, left_bound+1)
        else:
            e = uniform(left_bound, right_bound)

        v[i] = float(e)
    return v
    

def find_vectors(tree: tree.DecisionTreeClassifier, nb_features: int):
    """find a set of vectors that go through every path in the tree `tree`."""
    vectors = []

    c0 = [ (-inf, inf) for i in range(nb_features) ]

    t = tree.tree_

    def aux(node, constraints):
        ## exhaustion : node/leaf
        if t.feature[node] != _tree.TREE_UNDEFINED:
            ## node case

            feature_index = t.feature[node]

            left_child_index = t.children_left[node]
            right_child_index = t.children_right[node]

            left_bound, right_bound = constraints[feature_index]
            cl = [ e if i!=feature_index else (left_bound, t.threshold[node]) for i, e in enumerate(constraints) ]
            cr = [ e if i!=feature_index else (t.threshold[node], right_bound) for i, e in enumerate(constraints) ]

            aux(left_child_index, cl)
            aux(right_child_index, cr)

        else:
            ## leaf case
            vectors.append(choose_vector(constraints))

    aux(node=0, constraints=c0)

    return vectors