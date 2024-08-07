# Author: Runqing Xu, Bohua Zhan

"""API for computing integrals."""

import json
from flask import request
from flask.json import jsonify
import os

import integral
from integral import compstate
from integral import slagle
from integral import parser
from integral import expr
from app.app import app

example_dir = os.path.join(os.path.dirname(os.path.dirname(__file__)), "examples")


@app.route("/api/integral-load-book-list", methods=['POST'])
def integral_load_book_list():
    # Load book list from index.json
    index_file_path = os.path.join(example_dir, "index.json")
    with open(index_file_path, 'r', encoding='utf-8') as f:
        f_data = json.load(f)

    return jsonify(f_data)


@app.route("/api/add-new-book", methods=['POST'])
def add_new_book():
    # add new book
    data = json.loads(request.get_data().decode('utf-8'))
    new_book_name = data['new_book_name']
    imports = data['imports']
    # load all books
    index_file_path = os.path.join(example_dir, "index.json")
    with open(index_file_path, 'r', encoding='utf-8') as f:
        f_data = json.load(f)
    if new_book_name in f_data['book_list']:
        res = {
            'status': "ok",
            'book_list': f_data['book_list']
        }
        return res
    # add book to book list
    tmp = {
        "content": [],
        "name": new_book_name,
        "imports": imports,
    }
    new_book_path = os.path.join(example_dir, new_book_name + '.json')
    with open(new_book_path, 'w', encoding='utf-8') as f:
        json.dump(tmp, f, indent=4, ensure_ascii=False, sort_keys=True)
    f_data['book_list'].append(new_book_name)
    with open(index_file_path, 'w', encoding='utf-8') as f:
        json.dump({'book_list': f_data['book_list']}, f, indent=4, ensure_ascii=False, sort_keys=True)
    res = {
        'status': "ok",
        'book_list': f_data['book_list']
    }
    return jsonify(res)


@app.route("/api/delete-books", methods=['POST'])
def delete_books():
    # add new book
    data = json.loads(request.get_data().decode('utf-8'))
    books = data['books']
    # load all books
    index_file_path = os.path.join(example_dir, "index.json")
    with open(index_file_path, 'r', encoding='utf-8') as f:
        f_data = json.load(f)
    for book_name in books:
        # delete book
        f_data['book_list'].remove(book_name)
        os.remove(os.path.join(example_dir, book_name + '.json'))
    with open(index_file_path, 'w', encoding='utf-8') as f:
        json.dump({'book_list': f_data['book_list']}, f, indent=4, ensure_ascii=False, sort_keys=True)
    res = {
        'status': 'ok',
        'book_list': f_data['book_list']
    }
    return jsonify(res)


@app.route("/api/integral-load-book-content", methods=['POST'])
def integral_load_book_content():
    data = json.loads(request.get_data().decode('utf-8'))
    file_name = os.path.join(example_dir, data['bookname'] + '.json')

    # Load raw data
    with open(file_name, 'r', encoding='utf-8') as f:
        f_data = json.load(f)

    # For each expression, load its latex form
    for item in f_data['content']:
        # Expressions in item
        if 'expr' in item:
            e = integral.parser.parse_expr(item['expr'])
            latex_str = integral.latex.convert_expr(e)
            item['latex_str'] = latex_str
        # Conditions in item
        if 'conds' in item:
            latex_conds = []
            for cond_str in item['conds']:
                cond = integral.parser.parse_expr(cond_str)
                latex_conds.append(integral.latex.convert_expr(cond))
            item['latex_conds'] = latex_conds
        # Table elements
        if item['type'] == 'table':
            new_table = list()
            funcexpr = integral.expr.Fun(item['name'], integral.expr.Var('x'))
            item['funcexpr'] = integral.latex.convert_expr(funcexpr)
            for x, y in item['table'].items():
                x = integral.parser.parse_expr(x)
                y = integral.parser.parse_expr(y)
                new_table.append({
                    'x': integral.latex.convert_expr(x),
                    'y': integral.latex.convert_expr(y)
                })
            item['latex_table'] = new_table
    return jsonify(f_data)


@app.route("/api/save-func-table", methods=['POST'])
def save_func_table():
    data = json.loads(request.get_data().decode('utf-8'))
    label, table, book_name = data['label'], data['table'], data['book']
    book_path = os.path.join(example_dir, book_name + '.json')
    with open(book_path, 'r', encoding='utf-8') as f:
        book_content = json.load(f)
    pos = label.split(".")[:-1]
    pos = [int(i) - 1 for i in pos]
    pos.reverse()

    def rec(content, locs, d):
        res = content
        if len(locs) == 0:
            res = {}
            for e in d:
                if e['x'] != '':
                    res[e['x']] = e['y']
        elif len(locs) == 1:
            p = locs.pop()
            res[p]['table'] = rec(content[p]['table'], locs, d)
        else:
            p = locs.pop()
            res[p]['content'] = rec(content[p]['content'], locs, d)
        return res

    book_content['content'] = rec(book_content['content'], pos, table)
    with open(book_path, 'w', encoding='utf-8') as f:
        json.dump(book_content, f, indent=4, ensure_ascii=False, sort_keys=True)
    return jsonify({
        'status': 'ok'
    })


@app.route("/api/delete-func-table-item", methods=['POST'])
def delete_func_table_item():
    data = json.loads(request.get_data().decode('utf-8'))
    label, selected_items, book_name = data['label'], data['selected_items'], data['book']
    book_path = os.path.join(example_dir, book_name + '.json')
    with open(book_path, 'r', encoding='utf-8') as f:
        book_content = json.load(f)
    pos = label.split(".")[:-1]
    pos = [int(i) - 1 for i in pos]
    pos.reverse()

    def rec(content, locs, remove_items):
        res = content
        if len(locs) == 0:
            for n in remove_items:
                del res[n]
        elif len(locs) == 1:
            p = locs.pop()
            res[p]['table'] = rec(content[p]['table'], locs, remove_items)
        else:
            p = locs.pop()
            res[p]['content'] = rec(content[p]['content'], locs, remove_items)
        return res

    book_content['content'] = rec(book_content['content'], pos, selected_items)
    with open(book_path, 'w', encoding='utf-8') as f:
        json.dump(book_content, f, indent=4, ensure_ascii=False, sort_keys=True)
    return jsonify({
        'status': 'ok'
    })


@app.route("/api/integral-book-add-item", methods=['POST'])
def book_add_item():
    data = json.loads(request.get_data().decode('utf-8'))
    book_path = os.path.join(example_dir, data['filename'] + '.json')
    index = data['index']
    item = data['item']
    with open(book_path, 'r', encoding='utf-8') as f:
        book = json.load(f)
    book['content'].insert(index, item)
    if item['type'] == 'problem':
        # check the existance of this problem
        problem_path = os.path.join(example_dir, item['path'] + '.json')
        problem_file = compstate.CompFile(data['filename'], item['path'])
        if os.path.exists(problem_path):
            with open(problem_path, 'r', encoding='utf-8') as f:
                problem = json.load(f)
            for i in problem['content']:
                problem_file.add_item(compstate.parse_item(problem_file, i))
        raw_fixes = item['fixes']
        fixes = dict()
        for fix in raw_fixes:
            fixes[fix['var']] = parser.parse_expr(fix['type'], fixes=fixes)
        goal = integral.parser.parse_expr(item['expr'], fixes=fixes)
        conds = [integral.parser.parse_expr(cond, fixes=fixes) for cond in item['conds']]
        problem_file.add_goal(goal, conds=conds, fixes=fixes)
        with open(problem_path, 'w', encoding='utf-8') as f:
            json.dump(problem_file.export(), f, indent=4, ensure_ascii=False, sort_keys=True)
    with open(book_path, 'w', encoding='utf-8') as f:
        json.dump(book, f, indent=4, ensure_ascii=False, sort_keys=True)
    return jsonify({'status': 'ok'})


@app.route("/api/integral-open-file", methods=['POST'])
def integral_open_file():
    data = json.loads(request.get_data().decode('utf-8'))
    file_name = os.path.join(example_dir, data['filename'] + '.json')
    with open(file_name, 'r', encoding='utf-8') as f:
        f_data = json.load(f)

    for item in f_data['content']:
        if 'problem' in item:
            problem = integral.parser.parse_expr(item['problem'])
            item['_problem_latex'] = integral.latex.convert_expr(problem)

    return jsonify(f_data)


@app.route("/api/integral-save-book-item", methods=['POST'])
def integral_save_book_item():
    data = json.loads(request.get_data().decode('utf-8'))
    book_path = os.path.join(example_dir, data['filename'] + '.json')
    index = data['index']
    item = data['item']
    with open(book_path, 'r', encoding='utf-8') as f:
        book = json.load(f)
    book['content'][index] = item
    with open(book_path, 'w', encoding='utf-8') as f:
        json.dump(book, f, indent=4, ensure_ascii=False, sort_keys=True)
    return jsonify({'status': 'ok'})


@app.route("/api/integral-save-file", methods=['POST'])
def integral_save_file():
    data = json.loads(request.get_data().decode('utf-8'))
    file_name = os.path.join(example_dir, data['filename'] + '.json')
    with open(file_name, 'w', encoding='utf-8') as f:
        json.dump({"content": data['content'], "name": data['filename']}, f, indent=4, ensure_ascii=False,
                  sort_keys=True)
    return jsonify({
        'status': 'ok'
    })


@app.route("/api/clear-item", methods=['POST'])
def clear_item():
    data = json.loads(request.get_data().decode('UTF-8'))
    book_name = data['book']
    filename = data['file']
    cur_id = data['cur_id']
    file = compstate.CompFile(book_name, filename)
    for item in data['content']:
        file.add_item(compstate.parse_item(file, item))
    label = compstate.Label(data['selected_item'])
    st: compstate.StateItem = file.content[cur_id]
    st.get_by_label(label).clear()
    res = {
        "status": "ok",
        "item": st.export(),
    }
    if isinstance(st, (compstate.Calculation)):
        if len(st.steps) == 0:
            res['selected_item'] = str(compstate.Label([]))
        else:
            res['selected_item'] = str(compstate.Label([len(st.steps) - 1]))
    return jsonify(res)


@app.route("/api/query-integral", methods=['POST'])
def query_integral():
    data = json.loads(request.get_data().decode('UTF-8'))
    book_name = data['book']
    filename = data['file']
    cur_id = data['cur_id']
    file = compstate.CompFile(book_name, filename)
    for item in data['content']:
        file.add_item(compstate.parse_item(file, item))
    label = compstate.Label(data['selected_item'])
    st: compstate.StateItem = file.content[cur_id]
    subitem = st.get_by_label(label)
    if isinstance(subitem, compstate.CalculationStep):
        integrals = subitem.res.separate_integral()
    elif isinstance(subitem, compstate.Calculation):
        integrals = subitem.start.separate_integral()
    elif isinstance(subitem, compstate.RewriteGoalProof):
        integrals = subitem.begin.start.separate_integral()
    else:
        return jsonify({
            "status": "error",
            "msg": "Selected item is not part of a calculation."
        })

    res = []
    for e, loc in integrals:
        res.append({
            "expr": str(e),
            "var_name": e.var,
            "body": str(e.body),
            "latex_expr": integral.latex.convert_expr(e),
            "latex_body": integral.latex.convert_expr(e.body),
            "loc": str(loc)
        })
    return jsonify({
        "status": "ok",
        "integrals": res
    })


@app.route("/api/query-latex-expr", methods=['POST'])
def query_latex_expr():
    """Find latex form of an expression."""
    data = json.loads(request.get_data().decode('UTF-8'))
    try:
        e = integral.parser.parse_expr(data['expr'])
        selected = integral.parser.parse_expr(data['selected_expr'])
        locs = e.find_subexpr(selected)
        assert len(locs) > 0
        if len(locs) > 1:
            print('Warning: multiple locations', flush=True)
        loc = locs[0]
        return jsonify({
            "status": "ok",
            "latex_expr": integral.latex.convert_expr(selected),
            "expr": str(selected),
            "loc": str(loc)
        })
    except Exception as e:
        return jsonify({
            "status": "fail",
            "exception": str(e)
        })


@app.route("/api/query-identities", methods=['POST'])
def query_identities():
    """Find list of identity rewerites for an expression."""
    data = json.loads(request.get_data().decode('UTF-8'))
    book_name = data['book']
    filename = data['file']
    cur_id = data['cur_id']
    file_content = data['content']
    file = compstate.CompFile(book_name, filename)
    for item in file_content:
        file.add_item(compstate.parse_item(file, item))
    label = compstate.Label(data['selected_item'])
    st: compstate.StateItem = file.content[cur_id]
    subitem = st.get_by_label(label)
    try:
        e = integral.parser.parse_expr(data['expr'], fixes=subitem.ctx.get_fixes())
        results = integral.rules.ApplyIdentity.search(e, subitem.ctx)
        json_results = []
        for res in results:
            json_results.append({
                "res": str(res),
                "latex_res": integral.latex.convert_expr(res)
            })
        return jsonify({
            "status": "ok",
            "latex_expr": integral.latex.convert_expr(e),
            "results": json_results
        })
    except Exception as e:
        print(e, flush=True)
        print("fail", flush=True)
        return jsonify({
            "status": "fail",
            "exception": str(e)
        })


@app.route("/api/add-function-definition", methods=['POST'])
def add_function_definition():
    data = json.loads(request.get_data().decode('UTF-8'))
    book_name = data['book']
    forSomething = data['for']
    eq = integral.parser.parse_expr(data['eq'])
    conds = list(integral.parser.parse_expr(cond) for cond in data['conds'])
    file = compstate.CompFile(book_name, data['file'])
    for item in data['content']:
        file.add_item(compstate.parse_item(file, item))
    file.add_definition(eq, conds=conds)
    return jsonify({
        "status": "ok",
        "state": file.export()['content'],
        "selected_item": str(compstate.Label(""))
    })


@app.route("/api/add-goal", methods=["POST"])
def add_goal():
    data = json.loads(request.get_data().decode('UTF-8'))
    book_name = data['book']
    filename = data['file']
    file = compstate.CompFile(book_name, filename)
    for item in data['content']:
        file.add_item(compstate.parse_item(file, item))
    goal = integral.parser.parse_expr(data['goal'])
    conds = list(integral.parser.parse_expr(cond) for cond in data['conds'])
    file.add_goal(goal, conds=conds)
    return jsonify({
        "status": "ok",
        "state": file.export()['content'],
        "selected_item": str(compstate.Label(""))
    })


@app.route("/api/proof-by-calculation", methods=["POST"])
def proof_by_calculation():
    data = json.loads(request.get_data().decode('UTF-8'))
    book_name = data['book']
    filename = data['file']
    cur_id = data['cur_id']
    file = compstate.CompFile(book_name, filename)
    for item in data['content']:
        file.add_item(compstate.parse_item(file, item))
    label = compstate.Label(data['selected_item'])
    st: compstate.StateItem = file.content[cur_id]
    subitem = st.get_by_label(label)
    if isinstance(subitem, compstate.Goal):
        subitem.proof_by_calculation()
        return jsonify({
            "status": "ok",
            "item": st.export(),
            "selected_item": str(compstate.Label(label.data + [0]))
        })
    else:
        return jsonify({
            "status": "error",
            "msg": "Selected item is not a goal."
        })


@app.route("/api/proof-by-induction", methods=["POST"])
def proof_by_induction():
    data = json.loads(request.get_data().decode('UTF-8'))
    book_name = data['book']
    filename = data['file']
    cur_id = data['cur_id']
    file = compstate.CompFile(book_name, filename)
    for item in data['content']:
        file.add_item(compstate.parse_item(file, item))
    label = compstate.Label(data['selected_item'])
    st: compstate.StateItem = file.content[cur_id]
    subitem = st.get_by_label(label)
    induct_var = data['induct_var']
    start = integral.parser.parse_expr(data['start'])
    if isinstance(subitem, compstate.Goal):
        proof = subitem.proof_by_induction(induct_var, start=start)
        proof.base_case.proof_by_calculation()
        proof.induct_case.proof_by_calculation()
        return jsonify({
            "status": "ok",
            "item": st.export(),
            "selected_item": str(compstate.Label(label.data + [0]))
        })
    else:
        return jsonify({
            "status": "error",
            "msg": "Selected item is not a goal."
        })


@app.route("/api/proof-by-rewrite-goal", methods=["POST"])
def proof_by_rewrite_goal():
    data = json.loads(request.get_data().decode('UTF-8'))
    book_name = data['book']
    filename = data['file']
    cur_id = data['cur_id']
    file = compstate.CompFile(book_name, filename)
    for item in data['content']:
        file.add_item(compstate.parse_item(file, item))
    label = compstate.Label(data['selected_item'])
    st: compstate.StateItem = file.content[cur_id]
    subitem = st.get_by_label(label)
    begin = integral.parser.parse_expr(data['begin'])
    if isinstance(subitem, compstate.Goal):
        # Find the goal corresponding to begin
        begin_goal = None
        for item in file.content[:cur_id]:
            if isinstance(item, compstate.Goal) and item.goal == begin:
                begin_goal = item
                break
        assert begin_goal is not None
        subitem.proof_by_rewrite_goal(begin=begin_goal)
        return jsonify({
            "status": "ok",
            "item": st.export(),
            "selected_item": str(compstate.Label(label.data + [0]))
        })


@app.route("/api/expand-definition", methods=["POST"])
def expand_definition():
    data = json.loads(request.get_data().decode('UTF-8'))
    book_name = data['book']
    filename = data['file']
    cur_id = data['cur_id']
    file = compstate.CompFile(book_name, filename)
    for item in data['content']:
        file.add_item(compstate.parse_item(file, item))
    label = compstate.Label(data['selected_item'])
    st: compstate.StateItem = file.content[cur_id]
    subitem = st.get_by_label(label)
    if isinstance(subitem, (compstate.CalculationStep, compstate.Calculation)):
        if isinstance(subitem, compstate.Calculation):
            e = subitem.start
        else:
            e = subitem.res
        results = integral.rules.ExpandDefinition.search(e, subitem.ctx)
        if len(results) == 1:
            sube, loc = results[0]
            if expr.is_fun(sube):
                rule = integral.rules.ExpandDefinition(sube.func_name)
            elif expr.is_var(sube):
                rule = integral.rules.ExpandDefinition(sube.name)
            else:
                raise TypeError
            if loc.data:
                rule = integral.rules.OnLocation(rule, loc)
            subitem.perform_rule(rule)
            return jsonify({
                "status": "ok",
                "item": st.export(),
                "selected_item": str(compstate.get_next_step_label(subitem, label))
            })
        else:
            choices = []
            for sube, loc in results:
                choices.append({
                    'subexpr': str(sube),
                    'latex_subexpr': integral.latex.convert_expr(sube),
                    'func_name': sube.func_name,
                    'loc': str(loc)
                })
            return jsonify({
                "status": "choose",
                "choices": choices
            })
    else:
        return jsonify({
            "status": "error",
            "msg": "Selected item is not part of a calculation."
        })


@app.route("/api/fold-definition", methods=["POST"])
def fold_definition():
    data = json.loads(request.get_data().decode('UTF-8'))
    book_name = data['book']
    filename = data['file']
    cur_id = data['cur_id']
    file = compstate.CompFile(book_name, filename)
    for item in data['content']:
        file.add_item(compstate.parse_item(file, item))
    label = compstate.Label(data['selected_item'])
    st: compstate.StateItem = file.content[cur_id]
    subitem = st.get_by_label(label)
    if isinstance(subitem, (compstate.CalculationStep, compstate.Calculation)):
        if isinstance(subitem, compstate.Calculation):
            e = subitem.start
        else:
            e = subitem.res
        results = integral.rules.FoldDefinition.search(e, subitem.ctx)
        if len(results) == 1:
            _, loc, func_name = results[0]
            rule = integral.rules.FoldDefinition(func_name)
            if loc.data:
                rule = integral.rules.OnLocation(rule, loc)
            subitem.perform_rule(rule)
            return jsonify({
                "status": "ok",
                "item": st.export(),
                "selected_item": str(compstate.get_next_step_label(subitem, label))
            })
        else:
            return jsonify({
                "status": "choose",
                "item": st.export(),
                "selected_item": str(compstate.get_next_step_label(subitem, label))
            })
    else:
        return jsonify({
            "status": "error",
            "msg": "Selected item is not part of a calculation."
        })


@app.route("/api/solve-equation", methods=["POST"])
def integral_solve_equation():
    data = json.loads(request.get_data().decode('UTF-8'))
    book_name = data['book']
    filename = data['file']
    cur_id = data['cur_id']
    file = compstate.CompFile(book_name, filename)
    for item in data['content']:
        file.add_item(compstate.parse_item(file, item))
    label = compstate.Label(data['selected_item'])
    st: compstate.StateItem = file.content[cur_id]
    subitem = st.get_by_label(label)
    facts = data['selected_facts']
    if len(facts) != 1:
        return jsonify({
            "status": "error",
            "msg": "Exactly one fact must be selected"
        })
    lhs: integral.expr.Expr
    for fact_label in facts:
        fact = st.get_by_label(integral.compstate.Label(fact_label))
        if isinstance(fact, compstate.CalculationStep):
            lhs = fact.res
        elif isinstance(fact, compstate.Calculation):
            lhs = fact.start
        else:
            return jsonify({
                "status": "error",
                "msg": "Selected fact is not part of a calculation."
            })

    if isinstance(subitem, (compstate.CalculationStep, compstate.Calculation)):
        rule = integral.rules.IntegrateByEquation(lhs)
        subitem.perform_rule(rule)
        return jsonify({
            "status": "ok",
            "item": st.export(),
            "selected_item": str(compstate.get_next_step_label(subitem, label))
        })
    else:
        return jsonify({
            "status": "error",
            "msg": "Selected item is not part of a calculation."
        })


@app.route("/api/perform-step", methods=["POST"])
def integral_perform_step():
    data = json.loads(request.get_data().decode('UTF-8'))
    book_name = data['book']
    filename = data['file']
    cur_id = data['cur_id']
    file = compstate.CompFile(book_name, filename)
    for item in data['content']:
        file.add_item(compstate.parse_item(file, item))
    label = compstate.Label(data['selected_item'])
    st: compstate.StateItem = file.content[cur_id]
    subitem = st.get_by_label(label)
    rule = compstate.parse_rule(data['rule'], subitem)
    if isinstance(rule, (integral.rules.ApplyInductHyp, integral.rules.DerivIntExchange,
                         integral.rules.IntSumExchange, integral.rules.SeriesEvaluationIdentity,
                         integral.rules.ExpandMatFunc)):
        rule = integral.rules.OnSubterm(rule)
    if isinstance(subitem, (compstate.CalculationStep, compstate.Calculation)):
        subitem.perform_rule(rule)
    elif isinstance(subitem, compstate.RewriteGoalProof):
        subitem.begin.perform_rule(rule)
    else:
        return jsonify({
            "status": "error",
            "msg": "Selected item is not part of a calculation."
        })
    return jsonify({
        "status": "ok",
        "item": st.export(),
        "selected_item": str(compstate.get_next_step_label(subitem, label))
    })


@app.route("/api/perform-slagle", methods=["POST"])
def integral_perform_slagle():
    data = json.loads(request.get_data().decode('UTF-8'))
    book_name = data['book']
    filename = data['file']
    cur_id = data['cur_id']
    file = compstate.CompFile(book_name, filename)
    for item in data['content']:
        file.add_item(compstate.parse_item(file, item))
    label = compstate.Label(data['selected_item'])
    st: compstate.StateItem = file.content[cur_id]
    subitem = st.get_by_label(label)
    if isinstance(subitem, compstate.Calculation):
        e = subitem.last_expr
    elif isinstance(subitem, compstate.CalculationStep):
        e = subitem.parent.last_expr
    else:
        raise NotImplementedError
    steps = slagle.Slagle(e).export_step()
    subitem.perform_rules(steps)
    return jsonify({
        "status": "ok",
        "item": st.export(),
        "selected_item": str(compstate.get_next_step_label(subitem, label))
    })


@app.route("/api/query-theorems", methods=["POST"])
def integral_query_theorems():
    data = json.loads(request.get_data().decode('UTF-8'))
    book_name = data['book']
    filename = data['file']
    cur_id = data['cur_id']
    file = compstate.CompFile(book_name, filename)
    for item in data['content']:
        file.add_item(compstate.parse_item(file, item))
    eqs = []
    for prev_item in file.content[:cur_id]:
        for eq in prev_item.get_facts():
            eqs.append({
                'eq': str(eq),
                'latex_eq': integral.latex.convert_expr(eq)
            })
    label = compstate.Label(data['selected_item'])
    st: compstate.StateItem = file.content[cur_id]
    subitem = st.get_by_label(label)
    for cond in subitem.ctx.get_conds().data:
        if cond.is_equals():
            eqs.append({
                'eq': str(cond),
                'latex_eq': integral.latex.convert_expr(cond)
            })
    return jsonify({
        "status": "ok",
        "theorems": eqs
    })


@app.route("/api/query-vars", methods=["POST"])
def integral_query_vars():
    data = json.loads(request.get_data().decode('UTF-8'))
    book_name = data['book']
    filename = data['file']
    cur_id = data['cur_id']
    file = compstate.CompFile(book_name, filename)
    for item in data['content']:
        file.add_item(compstate.parse_item(file, item))
    label = compstate.Label(data['selected_item'])
    st: compstate.StateItem = file.content[cur_id]
    subitem = st.get_by_label(label)
    if isinstance(subitem, (compstate.CalculationStep, compstate.Calculation)):
        res = subitem.res if isinstance(subitem, compstate.CalculationStep) else subitem.start
    elif isinstance(subitem, compstate.RewriteGoalProof):
        res = subitem.begin.start
    else:
        return jsonify({
            "status": "error",
        })
    vars = list(res.get_vars())
    query_vars = []
    for var in vars:
        query_vars.append({'var': var, 'expr': ""})
    return jsonify({
        "status": "ok",
        "query_vars": query_vars
    })


@app.route("/api/query-expr", methods=['POST'])
def integral_query_expr():
    data = json.loads(request.get_data().decode('UTF-8'))
    try:
        e = integral.parser.parse_expr(data['expr'])
        return jsonify({
            "status": "ok",
            "latex_expr": integral.latex.convert_expr(e)
        })
    except Exception as e:
        return jsonify({
            "status": "fail",
            "exception": str(e)
        })


@app.route("/api/query-last-expr", methods=["POST"])
def integral_query_last_expr():
    # Query selected expression according to label
    data = json.loads(request.get_data().decode('UTF-8'))
    book_name = data['book']
    filename = data['file']
    cur_id = data['cur_id']
    file = compstate.CompFile(book_name, filename)
    for item in data['content']:
        file.add_item(compstate.parse_item(file, item))
    label = compstate.Label(data['selected_item'])
    st: compstate.StateItem = file.content[cur_id]
    subitem = st.get_by_label(label)
    if isinstance(subitem, (compstate.CalculationStep, compstate.Calculation)):
        res = subitem.res if isinstance(subitem, compstate.CalculationStep) else subitem.start
    elif isinstance(subitem, compstate.RewriteGoalProof):
        res = subitem.begin.start
    else:
        return jsonify({
            "status": "error",
        })
    return jsonify({
        "last_expr": str(res),
        "latex_expr": integral.latex.convert_expr(res),
        "status": "ok",
    })
