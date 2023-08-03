"""Setup flask app."""
from flask_cors import CORS

from datetime import date, datetime
from flask.json.provider import DefaultJSONProvider
from flask import Flask

class UpdatedJSONProvider(DefaultJSONProvider):
    def default(self, o):
        if isinstance(o, date) or isinstance(o, datetime):
            return o.isoformat(' ')
        return super().default(o)

app = Flask(__name__, static_url_path='/static')
app.json = UpdatedJSONProvider(app)
CORS(app)
app.secret_key = b'_5#y2L"F4Q8z\n\xec]/'