from sklearn.datasets import load_iris
from sklearn import tree

from dt_explanation import explain


def main():
    """Example of how to use the Decision Tree explanation module.
    This example uses the iris dataset from `sklearn.datasets`."""
    
    ## the name of the temp file used to give data to ocaml.
    filename_ = "output.txt"

    ## load data
    iris = load_iris()
    X = iris['data']
    y = iris['target']
    dt = tree.DecisionTreeClassifier(random_state=0, max_depth=2)
    dt = dt.fit(X, y)

    ## create vector
    v = X[0]

    res_obj = explain(dt, v, feature_names=iris['feature_names'], data_filename=filename_, verbose=True)
    print(res_obj)


if __name__ == "__main__":
    main()



# # Split dataset into training set and test set
# X_train, X_test, y_train, y_test = train_test_split(X, y, test_size=0.3, random_state=1) # 70% training and 30% test

# # Create Decision Tree classifer object
# clf = DecisionTreeClassifier()

# # Train Decision Tree Classifer
# clf = clf.fit(X_train,y_train)

# # Predict the response for test dataset
# y_pred = clf.predict(X_test)

