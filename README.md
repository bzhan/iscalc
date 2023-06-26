## iscalc - An interactive symbolic computation framework

Progress on the textbook *Inside Interesting Integrals* is summarized [here](InterestingIntegrals.md).

### Installation and usage:

This project requires Python 3.9 or greater and npm:

https://www.python.org/download/releases/3.0/:

https://www.npmjs.com/

Required packages are listed in requirements.txt. To install required packages in the
global environment, you can use:

```python -m pip install -r requirements.txt```

Depending on your system, may need to replace python by python3 or python3.x.

To avoid conflicts between projects that require different versions of packages,
we recommend installing Python packages in an isolated environment, e.g.
when using the `bash` shell, in the repository root directory do:

```
$ python3 -m venv ENV                 # Run python3.9 or above.
$ source ENV/bin/activate             # Sets up "python" to be your python3.
$ python -m pip install -r requirements.txt
$ python app.py                       # Runs the backend server on localhost:5000
```

In this same shell you can restore your previous environment later with

```$ deactivate```

The user interface is built using Vue, in the `./app` folder. To set up and
run the user interface server, in a different terminal
change to `./app` and use ```npm install``` followed by ```npm run serve```.

In your browser the user interface is at page `localhost:8080`.
