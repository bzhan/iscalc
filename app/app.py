"""Setup flask app."""
from flask_cors import CORS
from flask import Flask


app = Flask(__name__, static_url_path='/static')
CORS(app)
app.secret_key = b'_5#y2L"F4Q8z\n\xec]/'