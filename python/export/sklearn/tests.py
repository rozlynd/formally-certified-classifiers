from sklearn.datasets import load_iris
from sklearn import tree
from sklearn.tree import _tree

from export_sklearn_data.export_tree import export_tree
from export_sklearn_data.export_vector import export_vector
from export_sklearn_data.export_features import export_features

from dt_explanation import explain


def test_features():
    iris = load_iris()
    X = iris['data']

    # export tree in string
    print("begin export...")
    r = export_features(X[0])
    print("export finished.")
    print("the result :\n")
    print(r)

def test_export_tree():

    # load data
    iris = load_iris()
    X = iris['data']
    y = iris['target']
    dt = tree.DecisionTreeClassifier(random_state=0, max_depth=2)
    dt = dt.fit(X, y)

    # export tree in string
    print("begin export...")
    r = export_tree(dt)
    print("export finished.")
    print("the result :\n")
    print(r)

    # export in file
    # print(f"writing it into {filename} ...")
    # write_str_in_file(filename, r)
    # print("writing is finished.")


def test_export_vector():

    # load data
    iris = load_iris()
    X = iris['data']
    y = iris['target']
    dt = tree.DecisionTreeClassifier(random_state=0, max_depth=2)
    dt = dt.fit(X, y)
    
    v = X[0]

    # export vector in string
    print("begin export...")
    r = export_vector(v)
    print("export finished.")
    print("the result :\n")
    print(r)


def test_complete():
    # load data
    iris = load_iris()
    X = iris['data']
    y = iris['target']
    dt = tree.DecisionTreeClassifier(random_state=0, max_depth=2)
    dt = dt.fit(X, y)

    v = X[0]

    explain(dt, v, verbose=True)




if __name__ == "__main__":
    test_features()



