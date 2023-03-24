<template>
  <div>
    <!-- Menu -->
    <b-navbar type="light" variant="info">
      <b-navbar-brand href="#" v-on:click='loadBookList'>Integral</b-navbar-brand>
      <b-navbar-nav>
        <b-nav-item-dropdown text="File" left>
          <b-dropdown-item href="#" v-on:click="addBook">Add new book</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click="deleteBook">Delete books</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click="saveFile">Save file</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click="addHeader">Add header</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click="addFuncDef">Add definition</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click="addProblem">Add problem</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click="addLemma">Add lemma</b-dropdown-item>
        </b-nav-item-dropdown>
        <b-nav-item-dropdown text="Proof" left>
          <b-dropdown-item href="#" v-on:click="clearItem">Clear</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click="applyRule('FullSimplify')">Simplify</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click="addFuncDef">Add definition</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click="addGoal">Add goal</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click="proofByCalculation">Proof by calculation</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click="proofByInduction">Proof by induction</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click="proofByRewriteGoal">Proof by rewrite goal</b-dropdown-item>
        </b-nav-item-dropdown>
        <b-nav-item-dropdown text="Limits" left>
          <b-dropdown-item href="#" v-on:click="applyRule('LHopital')">L'Hopital Rule</b-dropdown-item>
        </b-nav-item-dropdown>
        <b-nav-item-dropdown text="Series" left>
          <b-dropdown-item href="#" v-on:click="applySeriesExpansion">Series expansion</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click="applyRule('SeriesEvaluationIdentity')">Series evaluation</b-dropdown-item>
        </b-nav-item-dropdown>
        <b-nav-item-dropdown text="Integral" left>
          <b-dropdown-item href="#" v-on:click="applyRule('IndefiniteIntegralIdentity')">Indefinite integral identity</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click="applyRule('ReplaceSubstitution')">Replace substitution</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click="applyRule('DefiniteIntegralIdentity')">Definite integral identity</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click="forwardSubstitution">Forward substitution</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click="backwardSubstitution">Backward substitution</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click="integrateByParts">Integrate by parts</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click="applyRule('ElimInfInterval')">Improper integral to limit</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click="applyRule('DerivIntExchange')">Exchange deriv and integral</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click="applyRule('IntSumExchange')">Exchange sum and integral</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click='splitRegion'>Splitting an Integral</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click="solveEquation">Solve equation</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click="slagleAlgo">Try Slagle</b-dropdown-item>
        </b-nav-item-dropdown>
        <b-nav-item-dropdown text="Rewrite" left>
          <b-dropdown-item href="#" v-on:click="rewriteEquation" id="rewriteEquation">Rewriting</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click="expandDefinition">Expand definition</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click="foldDefinition">Fold definition</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click="applyExpandPolynomial">Expand polynomial</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click="rewriteUsingIdentity" id="rewriteUsingIdentity">Apply identity</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click="applyTheorem">Apply lemma</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click="applyRule('ApplyInductHyp')">Apply inductive hyp</b-dropdown-item>
        </b-nav-item-dropdown>
        <b-nav-item-dropdown text="Equation" left>
          <b-dropdown-item href="#" v-on:click="variableSubstitution">Variable substitution</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click="applyLimitBothSides">Take limit on both sides</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click="applyDerivBothSides">Differentiate both sides</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click="applyRule('IntegrateBothSide')">Integrate both sides</b-dropdown-item>
          <b-dropdown-item href="#" v-on:click="solveEquation2">Solve equation</b-dropdown-item>
        </b-nav-item-dropdown>
      </b-navbar-nav>
    </b-navbar>
    <!-- Content of the file -->
    <div id="content">
      <div v-if="content_state === false" align=left>
        <div v-for="name in book_list" v-bind:key=name style="margin:5px 10px">
          <a href="#" v-on:click="openBook(name)">{{ name }}</a>
        </div>
      </div>
      <div v-if="content_state === true">
        <div v-for="(item, index) in content" :key="index" style="margin:5px 10px">
          <div v-if="'type' in item && item.type == 'FuncDef'">
            <div class="math-text">Definition</div>
            <MathEquation
              v-on:click.native="initialize(index)"
              v-bind:data="'\\(' + item.latex_eq + '\\)'"
              style="cursor:pointer"/>
          </div>
          <div v-if="'type' in item && item.type == 'Lemma'">
            <div class="math-text">Lemma</div>
            <MathEquation
              v-on:click.native="initialize(index)"
              v-bind:data="'\\(' + item.latex_eq + '\\)'"
              style="cursor:pointer"/>
          </div>
          <div v-if="'type' in item && item.type == 'Goal'">
            <div class="math-text">Goal</div>
            <MathEquation
              v-on:click.native="initialize(index)"
              v-bind:data="'\\(' + item.latex_goal + '\\)'"
              style="cursor:pointer"/>
          </div>
          <div v-if="'type' in item && item.type == 'Calculation'">
            <div class="math-text">Calculate</div>
            <MathEquation
              v-on:click.native="initialize(index)"
              v-bind:data="'\\(' + item.latex_start + '\\)'"
              style="cursor:pointer"/>
          </div>
        </div>
      </div>
    </div>
    <!-- Main panel showing calculation -->
    <div v-if="content.length > 0 && cur_id !== undefined" id="problem">
      <div v-if="'type' in content[cur_id] && content[cur_id].type == 'FuncDef'">
        <FuncDef v-bind:item="content[cur_id]" v-bind:label="''"
          v-bind:selected_item="selected_item"
          v-bind:selected_facts="selected_facts"/>
      </div>
      <div v-if="'type' in content[cur_id] && content[cur_id].type == 'Lemma'">
        <Lemma v-bind:item="content[cur_id]" v-bind:label="''"
          v-bind:selected_item="selected_item"
          v-bind:selected_facts="selected_facts"/>
      </div>
      <div v-if="'type' in content[cur_id] && content[cur_id].type == 'Goal'">
        <Goal v-bind:item="content[cur_id]" v-bind:label="''"
          @select="selectItem"
          @select_fact="selectFact"
          v-bind:selected_item="selected_item"
          v-bind:selected_facts="selected_facts"/>
      </div>
      <div v-if="'type' in content[cur_id] && content[cur_id].type == 'Calculation'">
        <Calculation v-bind:item="content[cur_id]" v-bind:label="''"
          @select="selectItem"
          @select_fact="selectFact"
          v-bind:selected_item="selected_item"
          v-bind:selected_facts="selected_facts"/>
      </div>
    </div>
    <!-- Main panel for showing book content-->
    <div v-if="content.length == 0" id="problem">
      <BookContent v-bind:content="book_content" @open_file='openFile' @select_table='selectTable'
        @select_header="selectHeader" v-bind:label="''" v-bind:selected_header="selected_header"
        v-bind:selected_table="selected_table" v-bind:header_level="1"></BookContent>
    </div>
    <div id="dialog">
      <div v-if="r_query_mode === 'edit func table'" style="margin: 5px">
        <table style="border-collapse: collapse">
          <tr>
            <td style="border-style: solid; padding: 3px">
              <MathEquation v-bind:data="'\\(' + '{x}' + '\\)'" />
            </td>
            <td v-for="(e, i) in selected_table_list" :key="i" style="border-style: solid; padding: 3px">
              <ExprQuery v-bind:value="e.x" @input="updateTable(i, $event, e.y)"></ExprQuery>
            </td>
          </tr>
          <tr>
            <td style="border-style: solid; padding: 3px">
              <MathEquation v-bind:data="'\\(' + selected_table_content.funcexpr + '\\)'" />
            </td>
            <td v-for="(e, i) in selected_table_list" :key="i" style="border-style: solid; padding: 3px">
              <ExprQuery v-bind:value="e.y" @input="updateTable(i, e.x, $event)"></ExprQuery>
            </td>
          </tr>
        </table>
        <button v-on:click="selected_table_list.push({ 'x': '', 'y': '' }); checkVal.push(false)">add</button>&nbsp;
        <button v-on:click="deleteSelectedTableItem()">delete</button>&nbsp;
        <button v-on:click="saveFuncTable()">save</button>
      </div>
      <div v-if="r_query_mode === 'add lemma'">
        <span class="math-text">Add lemma:</span><br />
        <span class="math-text">type:</span>&nbsp;
        <select v-model="lemma_type">
          <option v-for="(type, index) in lemma_types" :key="index">{{ type }}</option>
        </select>
        <div v-if="lemma_type !== 'table'">
          <span class="math-text">category:</span>&nbsp;
          <select v-model="lemma_category">
            <option v-for="(category, index) in lemma_categories" :key="index">{{ category }}</option>
          </select>
          <ExprQuery v-model="expr_query1"/><br/>
          <div v-for="(cond, index) in cond_query" :key="index">
            <ExprQuery v-bind:value="cond" @input="setCondQuery(index, $event)"/><br/>
          </div>
          <span class="math-text">reference:</span>&nbsp;
          <input v-model="msg"/><br/>
          <button v-on:click="doAddLemma">OK</button>&nbsp;
          <button v-on:click="cond_query.push('')">Add condition</button>
        </div>
        <div v-if="lemma_type === 'table'">
          <span class="math-text">function name:</span>&nbsp;
          <input v-model="func_table_name"/>
          <div v-for="(arg, i) in func_table['args']" :key="i">
            <span class="math-text">argument:</span>&nbsp;
            <ExprQuery v-bind:value="arg" @input="setFunArg(i, $event)"></ExprQuery>
            <span class="math-text">value:</span>&nbsp;
            <ExprQuery v-bind:value="func_table['values'][i]" @input="setFunVal(i, $event)"></ExprQuery>
          </div><br/>
          <button v-on:click="doAddLemma">OK</button>&nbsp;
          <button v-on:click="func_table['args'].push(''); func_table['values'].push('');">add item</button>
        </div>
      </div>
      <div v-if="r_query_mode === 'add header'">
        <span class="math-text">Add header:</span><br />
        <input v-model="header" />
        <button v-on:click="doAddHeader">OK</button>
      </div>
      <div v-if="r_query_mode === 'add definition'">
        <span class="math-text">Add function definition:</span><br />
        <ExprQuery v-model="expr_query1" /><br />
        <div v-for="(cond, index) in cond_query" :key="index">
          <ExprQuery v-bind:value="cond" @input="setCondQuery(index, $event)" /><br />
        </div>
        <button v-on:click="doAddFuncDef('file')">OK</button>&nbsp;
        <button v-on:click="cond_query.push('')">Add condition</button>
      </div>
      <div v-if="r_query_mode === 'add definition for book'">
        <span class="math-text">Add function definition:</span><br />
        <ExprQuery v-model="expr_query1" /><br />
        <div v-for="(cond, index) in cond_query" :key="index">
          <ExprQuery v-bind:value="cond" @input="setCondQuery(index, $event)" /><br />
        </div>
        <span class="math-text">file name:</span>
        <input v-model="msg" /><br />
        <button v-on:click="doAddFuncDef('book')">OK</button>&nbsp;
        <button v-on:click="cond_query.push('')">Add condition</button>
      </div>
      <div v-if="r_query_mode === 'add goal' || r_query_mode === 'add problem'">
        <span v-if="r_query_mode === 'add goal'" class="math-text">Add goal:</span>
        <span v-if="r_query_mode === 'add problem'" class="math-text">Add problem:</span><br />
        <ExprQuery v-model="expr_query1" /><br />
        <div v-for="(cond, index) in cond_query" :key="index">
          <ExprQuery v-bind:value="cond" @input="setCondQuery(index, $event)" /><br />
        </div>
        <div v-if="r_query_mode === 'add problem'">
          <span class="math-text">file name:</span>
          <input v-model="msg" />
        </div>
        <button v-if="r_query_mode === 'add goal'" v-on:click="doAddGoal">OK</button>
        <button v-if="r_query_mode === 'add problem'" v-on:click="doAddProblem">OK</button>&nbsp;
        <button v-on:click="cond_query.push('')">Add condition</button>
      </div>
      <div v-if="r_query_mode === 'add book'">
        <span class="math-text">book name:</span>
        <input type="text" v-model="new_book_name" style="width: 190.4px;height: 32px;" />
        <button v-on:click="doAddBook()">OK</button>
      </div>
      <div v-if="r_query_mode === 'delete book'">
        <button v-on:click="showDeleteDialog()" v-show="!show_delete_book_msg">Delete</button>
        <div class="mask" v-show="show_delete_book_msg">
          <span>are you sure to delete these books ?</span><br />
          <button class="app-download" @click="doDeleteBook">YES</button>
          <button class="app-download" @click="cancelDelete">NO</button>
        </div>

      </div>
      <div v-if="r_query_mode === 'apply induction'">
        <span class="math-text">Please specify induction variable</span><br />
        <input v-model="induct_var"><br />
        <span class="math-text">starting from</span><br />
        <ExprQuery v-model="expr_query1" />
        <button v-on:click="doApplyInduction">OK</button>
      </div>
      <div v-if="r_query_mode === 'apply rewrite goal'">
        <div class="math-text">Select lemma to start from:</div>
        <div v-for="(item, index) in theorems" :key="index"
             v-on:click="doApplyRewriteGoal(index)" style="cursor:pointer">
          <MathEquation v-bind:data="'\\(' + item.latex_eq + '\\)'" />
        </div>
      </div>
      <div v-if="r_query_mode === 'integrate by parts'">
        <span class="math-text">Integrate by parts on: </span>
        <MathEquation v-bind:data="'\\(' + sep_int[0].latex_body + '\\)'" /><br />
        <MathEquation data="Choose \(u\) and \(v\) such that \(u\cdot\mathrm{d}v\) is the integrand." />
        <div>
          <MathEquation data="\(u=\)" />
          <ExprQuery v-model="expr_query1" />
        </div>
        <div>
          <MathEquation data="\(v=\)" />
          <ExprQuery v-model="expr_query2" /><br />
        </div>
        <button v-on:click="doIntegrateByParts">OK</button>
      </div>
      <div v-if="r_query_mode === 'forward substitution'">
        <MathEquation v-bind:data="'\\(' + sep_int[int_id].latex_expr + '\\)'" /><br />
        <span class="math-text">Location: {{ sep_int[int_id].loc }}</span><br />
        <button v-bind:disabled='int_id == 0' v-on:click="int_id--">prev</button>
        <button v-bind:disabled='int_id == sep_int.length - 1' v-on:click='int_id++'>next</button><br />
        <span class="math-text">Substitution on: </span>
        <MathEquation v-bind:data="'\\(' + sep_int[int_id].latex_body + '\\)'" /><br />
        <span class="math-text">Substitute </span>
        <input v-model="subst_var"><br />
        <span class="math-text"> for</span><br />
        <ExprQuery v-model="expr_query1" /><br />
        <button v-on:click="doForwardSubstitution">OK</button>
      </div>
      <div v-if="r_query_mode === 'backward substitution'">
        <span class="math-text">Backward substitution on: </span>
        <MathEquation v-bind:data="'\\(' + sep_int[int_id].latex_body + '\\)'" /><br />
        <span class="math-text">Location: {{ sep_int[int_id].loc }}</span><br />
        <button v-bind:disabled='int_id == 0' v-on:click="int_id--">prev</button>
        <button v-bind:disabled='int_id == sep_int.length - 1' v-on:click='int_id++'>next</button><br />
        <span class="math-text">New variable </span>
        <input v-model="subst_var"><br />
        <span class="math-text">Substitute </span>
        <span class="math-text-italic">{{ sep_int[int_id].var_name }}</span>
        <span class="math-text"> for</span><br />
        <ExprQuery v-model="expr_query1" /><br />
        <button v-on:click="doBackwardSubstitution">OK</button>
      </div>
      <div v-if="r_query_mode === 'rewrite equation'">
        <div class="math-text">Select subexpression:</div>
        <input
             class="item-text" ref="select_expr1"
             v-bind:value="lastExpr"
             style="width:500px" disabled="disabled"
          @select="selectExpr"><br />
        &nbsp;<MathEquation v-bind:data="'\\(' + latex_selected_expr + '\\)'" class="indented-text"/><br/>
        <span class="math-text">Rewrite subexpression to</span><br />
        <ExprQuery v-model="expr_query1" />
        <button v-on:click="doRewriteEquation">OK</button>
      </div>
      <div v-if="r_query_mode === 'rewrite using identity'">
        <div class="math-text">Select subexpression:</div>
        <input
             class="item-text" ref="select_expr1"
             v-bind:value="lastExpr"
             style="width:500px" disabled="disabled"
          @select="selectExprIdentity"><br />
        &nbsp;<MathEquation v-bind:data="'\\(' + latex_selected_expr + '\\)'" class="indented-text"/><br/>
        <div v-for="(item, index) in identity_rewrites" :key="index">
          <MathEquation
            v-on:click.native="applyIdentity(index)"
            v-bind:data="'\\(=' + item.latex_res + '\\)'"
            style="cursor:pointer" />
        </div>
      </div>
      <div v-if="r_query_mode === 'split region'">
        <div class="math-text">Split region at:</div>
        <ExprQuery v-model="expr_query1" />
        <button v-on:click="doSplitRegion">OK</button>
      </div>
      <div v-if="r_query_mode === 'select theorem'">
        <div class="math-text">Select subexpression:</div>
        <input
             class="item-text" ref="select_expr1"
             v-bind:value="lastExpr"
             style="width:500px" disabled="disabled"
          @select="selectExpr"><br />
        &nbsp;<MathEquation v-bind:data="'\\(' + latex_selected_expr + '\\)'" class="indented-text"/><br/>
        <div class="math-text">Select theorem to apply:</div>
        <div v-for="(item, index) in theorems" :key="index"
             v-on:click="doApplyTheorem(index)" style="cursor:pointer">
          <MathEquation v-bind:data="'\\(' + item.latex_eq + '\\)'" />
        </div>
      </div>
      <div v-if="r_query_mode === 'query vars'">
        <div class="math-text">Enter instantiation in theorem</div>
        <div v-for="(item, index) in query_vars" :key="index">
          <MathEquation v-bind:data="'\\(' + item.var + '\\to \\)'" />
          <ExprQuery v-model="item.expr" />
        </div>
        <button v-on:click="doVariableSubstitution">OK</button>
      </div>
      <div v-if="r_query_mode === 'derivate both sides'">
        <span class="math-text">Please specify variable</span><br />
        <input v-model="deriv_var">
        <button v-on:click="doApplyDerivBothSides">OK</button>
      </div>
      <div v-if="r_query_mode === 'solve equation'">
        <div class="math-text">Select subexpression to solve for:</div>
        <input
             class="item-text" ref="select_expr1"
             v-bind:value="lastExpr"
             style="width:500px" disabled="disabled"
          @select="selectExpr"><br />
        &nbsp;<MathEquation v-bind:data="'\\(' + latex_selected_expr + '\\)'" class="indented-text"/><br/>
        <button v-on:click="doSolveEquation">Solve</button>
      </div>
      <div v-if="r_query_mode === 'limit both sides'">
        <span class="math-text">Take limit as variable</span><br />
        <input v-model="limit_var">
        <span class="math-text">goes to</span><br />
        <ExprQuery v-model="expr_query1" />
        <button v-on:click="doApplyLimitBothSides">OK</button>
      </div>
      <div v-if="r_query_mode === 'series expansion'">
        <div class="math-text">Series expansion on:</div>
        <input
             class="item-text" ref="select_expr1"
             v-bind:value="lastExpr"
             style="width:500px" disabled="disabled"
          @select="selectExpr"><br />
        &nbsp;<MathEquation v-bind:data="'\\(' + latex_selected_expr + '\\)'" class="indented-text"/><br/>
        <span class="math-text">Index variable</span><br />
        <input v-model="index_var">
        <button v-on:click="doApplySeriesExpansion">OK</button>
      </div>
      <div v-if="r_query_mode === 'expand polynomial'">
        <div class="math-text">Expand polynomial on:</div>
        <input
             class="item-text" ref="select_expr1"
             v-bind:value="lastExpr"
             style="width:500px" disabled="disabled"
          @select="selectExpr"><br />
        &nbsp;<MathEquation v-bind:data="'\\(' + latex_selected_expr + '\\)'" class="indented-text"/><br/>
        <button v-on:click="doApplyExpandPolynomial">OK</button>
      </div>
      <div v-if="r_query_mode === 'expand definition'">
        <div class="math-text">Expand definition on:</div>
        <div v-for="(item, index) in def_choices" :key="index"
             v-on:click="doExpandDefinition(index)" style="cursor:pointer">
          <MathEquation v-bind:data="'\\(' + item.latex_subexpr + '\\)'" />
        </div>
      </div>
    </div>
    <div id="select">
      <div v-if="r_query_mode === 'edit func table'">
        <div v-for="(entry, i) in selected_table_list" :key="i" style="margin:5px 10px">
          <label :for="'entry_' + entry.x" @change="selectTableItem(i, entry.x)">
            <input type="checkbox" :id="'entry_' + entry.x" v-model="checkVal[i]">{{ entry.x }}
          </label><br/>
        </div>
      </div>
      <div v-if="r_query_mode === 'add book'">
        <span class="math-text">select books to import:</span><br />
      </div>
      <div v-if="r_query_mode === 'delete book'">
        <span class="math-text">select books to delete:</span><br />
      </div>
      <div v-if="r_query_mode === 'add book' || r_query_mode === 'delete book'">
        <div v-for="(name, i) in book_list" :key="i" style="margin:5px 10px">
          <label :for="'book_' + name" @change="selectBook(i, name)">
            <input type="checkbox" :id="'book_' + name" v-model="checkVal[i]">{{ name }}
          </label><br />
        </div>
      </div>
      <div v-if="r_query_mode === 'add lemma' && lemma_type !== 'table'">
        <span class="math-text">lemma's attributes</span>
        <div v-for="(attr, i) in lemma_attributes" :key="i" style="margin:5px 10px">
          <label :for="'attribute_' + attr" @change="selectAttribute(i, attr)">
            <input type="checkbox" :id="'attribute_' + attr" v-model="checkVal[i]">{{ attr }}
          </label><br />
        </div>
      </div>
    </div>
  </div>
</template>

<script>
import axios from 'axios'
import MathEquation from '../util/MathEquation.vue'
import FuncDef from './FuncDef.vue'
import ExprQuery from './ExprQuery.vue'
import Goal from "./Goal.vue"
import Lemma from "./Lemma.vue"
import Calculation from "./Calculation.vue"
import BookContent from "./BookContent.vue"

export default {
  name: 'Integral',
  components: {
    MathEquation,
    FuncDef,
    Goal,
    Calculation,
    ExprQuery,
    Lemma,
    BookContent,
  },

  props: [
  ],

  data: function () {
    return {
      // Display list of books (false) or list of items in a file.
      content_state: undefined,

      // List of integral books
      book_list: [],
      // Currently open book
      book_name: "interesting",
      // Content of the currently opened book
      book_content: {},

      // Currently opened file
      filename: undefined,
      // List of problems in the file
      content: [],
      // ID of the selected item
      cur_id: undefined,

      // Current query mode
      r_query_mode: undefined,

      // All separate integrals
      sep_int: [],

      // List of choices for fold/unfold definition
      def_choices: [],

      // Selected goal
      selected_item: undefined,

      // Query for expressions
      expr_query1: undefined,
      expr_query2: undefined,

      // Query for conditions
      cond_query: [],

      // Query for substitution variable
      subst_var: undefined,

      // Query for induction variable
      induct_var: undefined,

      // Query for variable to differentiate
      deriv_var: undefined,

      // Query for limit variable
      limit_var: undefined,

      // Query for index variable
      index_var: 'n',

      // Selected fact
      selected_facts: {},

      // Selected latex expression
      selected_expr: undefined,
      latex_selected_expr: undefined,
      selected_loc: undefined,

      // List of identity rewrites for selected expression
      identity_rewrites: [],

      // List of theorems
      theorems: undefined,

      // Query for variable instantiation
      query_vars: undefined,

      // Expression in the chosen step
      last_expr: undefined,

      // the index of sep-integrals
      int_id: 0,

      // Selected book
      selected_book: [],
      checkVal: [],
      show_delete_book_msg: false,

      // add book
      new_book_name: "",

      // selected header
      header: "",
      selected_header: undefined,

      //add problem, definition for book
      msg: "",

      //add lemma
      lemma_types: ['inequality', 'axiom', 'table', 'unknown'],
      lemma_categories: ['trigonometric', 'exp-log', 'power', 'binomial', 'unknown'],
      lemma_attributes: ['simplify', 'bidirectional'],
      lemma_type: undefined,
      lemma_category: undefined,
      selected_lemma_attributes: [],
      selected_table: undefined,
      func_table: { args: [], values: [] },
      func_table_name: "",

      //edit table
      selected_table_content: undefined,
      selected_table_item_list: [],
      selected_table_list: [],
    }
  },

  computed: {
    lastExpr: function () {
      if (this.content.length > 0 && this.cur_id !== undefined) {
        this.query_last_expr()
        return this.last_expr
      } else {
        return ""
      }
    }
  },

  methods: {
    loadBookList: async function () {
      const response = await axios.post('http://127.0.0.1:5000/api/integral-load-book-list')
      this.book_list = response.data.book_list
      this.content_state = false
      this.content = []
      this.cur_id = undefined
      this.filename = undefined
    },

    loadBookContent: async function () {
      const data = {
        bookname: this.book_name
      }
      const response = await axios.post('http://127.0.0.1:5000/api/integral-load-book-content', JSON.stringify(data))
      this.book_content = response.data
      console.log(this.book_content)
    },

    openBook: async function (book_name) {
      this.book_name = book_name
      this.r_query_mode = undefined
      this.loadBookContent()
    },

    query_last_expr: async function () {
      const data = {
        book: this.book_name,
        file: this.filename,
        content: this.content,
        cur_id: this.cur_id,
        selected_item: this.selected_item
      }
      const response = await axios.post("http://127.0.0.1:5000/api/query-last-expr", JSON.stringify(data))
      if (response.data.status === 'ok') {
        this.last_expr = response.data.last_expr
      } else {
        this.last_expr = ""
      }
    },
    saveFile: async function () {
      if (this.filename === undefined)
        return
      const data = {
        filename: this.filename,
        content: this.content
      }
      const response = await axios.post("http://127.0.0.1:5000/api/integral-save-file", JSON.stringify(data))
      if (response.data.status === 'ok') {
        console.log("ok")
      }
    },
    openFile: async function (filename) {
      const data = {
        filename: filename
      };
      this.filename = filename
      const response = await axios.post("http://127.0.0.1:5000/api/integral-open-file", JSON.stringify(data))
      this.content = response.data.content
      this.cur_id = undefined
      this.content_state = true
      this.selected_header = undefined
      this.r_query_mode = undefined
    },

    initialize: async function (index) {
      this.r_query_mode = undefined
      this.cur_id = index
      this.selected_item = undefined
      this.selected_facts = {}
    },
    // add lemma
    addLemma: function () {
      if (this.selected_header === undefined)
        return
      this.r_query_mode = "add lemma"
      this.checkVal = []
      for (let i = 0; i < this.lemma_attributes.lenth; i++) {
        this.checkVal.add(false)
      }
      this.lemma_type = 'axiom'
      this.lemma_category = 'unknown'
      this.msg = ""
      this.selected_lemma_attributes = []
      this.cond_query = []
      this.expr_query1 = ""
      this.func_table_name = ""
      this.func_table = { args: [], values: [] }
    },
    doAddLemma: async function () {
      const data = {
        lemma_type: this.lemma_type,
        book_name: this.book_name,
        lemma_category: this.lemma_category,
        reference: this.msg,
        lemma_attributes: this.selected_lemma_attributes,
        expr: this.expr_query1,
        conds: this.cond_query,
        table: this.func_table,
        table_name: this.func_table_name,
        label: this.selected_header,
      }
      const response = await axios.post("http://127.0.0.1:5000/api/book-add-lemma", JSON.stringify(data))
      if (response.data.status == 'ok') {
        this.r_query_mode = undefined
        this.expr_query1 = ''
        this.cond_query = []
        this.msg = ""
        this.loadBookContent()
        this.book_name = response.data.book_name
      }
    },
    selectAttribute: function (i, attr) {
      if (this.checkVal[i] && !this.selected_lemma_attributes.includes(attr)) {
        this.selected_lemma_attributes.push(attr)
      } else if (!this.checkVal[i] && this.selected_lemma_attributes.includes(attr)) {
        this.selected_lemma_attributes.splice(this.selected_lemma_attributes.findIndex(j => j == attr))
      }
      console.log(this.selected_lemma_attributes)
    },
    selectTable: function (content, label) {
      this.selected_table = label
      this.selected_table_content = content
      this.selected_table_list = []
      this.selected_table_item_list = []
      this.checkVal = []
      for (let k in content.table) {
        this.checkVal.push(false)
        this.selected_table_list.push({ 'x': k, 'y': content.table[k] })
      }
      this.r_query_mode = 'edit func table'
      console.log("selected_table:")
      console.log(this.selected_table_list)
      console.log(content)
      console.log(label)
    },
    selectTableItem: function (i, name) {
      console.log(this.checkVal[i], this.selected_table_item_list.includes(name),name,i)
      if (this.checkVal[i] && !this.selected_table_item_list.includes(name)) {
        this.selected_table_item_list.push(name)
      } 
      if (!this.checkVal[i] && this.selected_table_item_list.includes(name)) {
        this.selected_table_item_list.splice(this.selected_table_item_list.findIndex(j => j == name))
      }
      console.log(this.selected_table_item_list)
    },
    deleteSelectedTableItem: async function () {
      const data = {
        label : this.selected_table,
        selected_items : this.selected_table_item_list,
        book : this.book_name
      }
      const response = await axios.post("http://127.0.0.1:5000/api/delete-func-table-item", JSON.stringify(data))
      if (response.data.status == 'ok') {
        this.r_query_mode = undefined
        this.loadBookContent()
      }
    },
    updateTable: function (idx, k, v) {
      this.selected_table_list[idx].x = k
      this.selected_table_list[idx].y = v
    },
    saveFuncTable: async function () {
      const data = {
        label : this.selected_table,
        table : this.selected_table_list,
        book : this.book_name
      }
      const response = await axios.post("http://127.0.0.1:5000/api/save-func-table", JSON.stringify(data))
      if (response.data.status == 'ok') {
        this.r_query_mode = undefined
        this.loadBookContent()
      }
    },

    // add problem
    addProblem: function () {
      if (this.selected_header !== undefined)
        this.r_query_mode = "add problem"
      this.expr_query1 = ''
      this.cond_query = []
      this.filename = ""
    },

    doAddProblem: async function () {
      const data = {
        book: this.book_name,
        file: this.msg,
        goal: this.expr_query1,
        conds: this.cond_query,
        label: this.selected_header
      }
      const response = await axios.post("http://127.0.0.1:5000/api/book-add-problem", JSON.stringify(data))
      if (response.data.status == 'ok') {
        this.r_query_mode = undefined
        this.expr_query1 = ''
        this.cond_query = []
        this.filename = ""
        this.loadBookContent()
      }
    },

    // Select an item
    selectItem: function (item_id) {
      console.log('selectItem', item_id)
      this.selected_item = item_id
      this.r_query_mode = undefined
    },

    // Select a fact
    selectFact: function (item_id) {
      console.log('selectFact', item_id)
      if (item_id in this.selected_facts) {
        this.$delete(this.selected_facts, item_id)
      } else {
        this.$set(this.selected_facts, item_id, true)
      }
    },

    // Restart proof, delete all steps
    clearItem: async function () {
      const data = {
        book: this.book_name,
        file: this.filename,
        content: this.content,
        cur_id: this.cur_id,
        selected_item: this.selected_item
      }
      if (this.selected_item === undefined) {
        data.selected_item = ""
      }
      const response = await axios.post("http://127.0.0.1:5000/api/clear-item", JSON.stringify(data))
      if (response.data.status == 'ok') {
        this.$set(this.content, this.cur_id, response.data.item)
        if ('selected_item' in response.data) {
          this.selected_item = response.data.selected_item
        }
      }
    },
    setFunArg: function (index, value) {
      this.$set(this.func_table['args'], index, value)
    },
    setFunVal: function (index, value) {
      this.$set(this.func_table['values'], index, value)
    },
    setCondQuery: function (index, value) {
      this.$set(this.cond_query, index, value)
    },

    // Add function definition
    addFuncDef: function () {
      if (this.filename === undefined && this.book_name !== undefined && this.selected_header !== undefined)
        this.r_query_mode = 'add definition for book'
      else if (this.filename !== undefined)
        this.r_query_mode = 'add definition'
      else
        this.r_query_mode = undefined
      this.expr_query1 = ''
      this.cond_query = []
    },

    // Perform add function definition
    doAddFuncDef: async function (forSomething) {
      if (forSomething == 'file') {
        const data = {
          book: this.book_name,
          file: this.filename,
          content: this.content,
          eq: this.expr_query1,
          conds: this.cond_query,
          for: "file"
        }
        const response = await axios.post("http://127.0.0.1:5000/api/add-function-definition", JSON.stringify(data))
        if (response.data.status == 'ok') {
          this.content = response.data.state
          this.cur_id = this.content.length - 1
          this.selected_item = response.data.selected_item
          this.r_query_mode = undefined
          this.expr_query1 = ''
          this.cond_query = []
        }
      }
      else if (forSomething == 'book') {
        const data = {
          book: this.book_name,
          eq: this.expr_query1,
          file: this.msg,
          label: this.selected_header,
          conds: this.cond_query,
          for: "book"
        }
        const response = await axios.post("http://127.0.0.1:5000/api/add-function-definition", JSON.stringify(data))
        if (response.data.status == 'ok') {
          this.r_query_mode = undefined
          this.expr_query1 = ''
          this.cond_query = []
          this.loadBookContent()
          this.book_name = response.data.book_name
        }
      }
    },

    // select header 
    selectHeader: function (header_id) {
      console.log("selected header:" + header_id)
      this.selected_header = header_id
      this.r_query_mode = undefined
    },

    // add header
    addHeader: function () {
      if (this.selected_header !== undefined)
        this.r_query_mode = "add header"
    },

    doAddHeader: async function () {
      const data = {
        header_name: this.header,
        book_name: this.book_name,
        label: this.selected_header
      }
      const response = await axios.post("http://127.0.0.1:5000//api/integral-add-header", JSON.stringify(data))
      if (response.data.status == 'ok') {
        this.r_query_mode = undefined
        this.header = ""
        this.loadBookContent()
      }
    },

    //Delete Books
    deleteBook: function () {
      this.r_query_mode = 'delete book'
      this.selected_book = []
      this.checkVal = []
      this.show_delete_book_msg = false
      for (let i = 0; i <= this.book_list.lenth; i++) {
        this.checkVal.add(false)
      }
    },
    cancelDelete: function () {
      this.show_delete_book_msg = false
      this.r_query_mode = undefined
    },
    doDeleteBook: async function () {
      const data = {
        books: this.selected_book
      }
      const response = await axios.post("http://127.0.0.1:5000/api/delete-books", JSON.stringify(data))
      if (response.data.status == 'ok') {
        this.book_list = response.data.book_list
        this.r_query_mode = undefined
        this.show_delete_book_msg = false
      }
    },
    showDeleteDialog: function () {
      this.show_delete_book_msg = true
    },

    selectBook: function (i, book_name) {
      if (this.checkVal[i] && !this.selected_book.includes(book_name)) {
        this.selected_book.push(book_name)
      } if (!this.checkVal[i] && this.selected_book.includes(book_name)) {
        this.selected_book.splice(this.selected_book.findIndex(j => j == book_name))
      }
      console.log(this.selected_book)
    },

    // Add book
    addBook: function () {
      this.r_query_mode = 'add book'
      this.selected_book = []
      this.checkVal = []
      for (let i = 0; i < this.book_list.lenth; i++) {
        this.checkVal.add(false)
      }
    },

    doAddBook: async function () {
      const data = {
        new_book_name: this.new_book_name,
        imports: this.selected_book
      }
      const response = await axios.post("http://127.0.0.1:5000/api/add-new-book", JSON.stringify(data))
      if (response.data.status == 'ok') {
        this.book_list = response.data.book_list
        this.r_query_mode = undefined
        this.content_state = false
        this.content = []
        this.new_book_name = undefined
      }
    },

    // Add goal
    addGoal: function () {
      this.r_query_mode = 'add goal'
    },

    // Perform add goal
    doAddGoal: async function () {
      const data = {
        book: this.book_name,
        file: this.filename,
        content: this.content,
        goal: this.expr_query1,
        conds: this.cond_query
      }
      const response = await axios.post("http://127.0.0.1:5000/api/add-goal", JSON.stringify(data))
      if (response.data.status == 'ok') {
        this.content = response.data.state
        this.cur_id = this.content.length - 1
        this.selected_item = response.data.selected_item
        this.r_query_mode = undefined
        this.expr_query1 = ''
        this.cond_query = []
      }
    },

    // Perform proof by calculation
    proofByCalculation: async function () {
      const data = {
        book: this.book_name,
        file: this.filename,
        content: this.content,
        cur_id: this.cur_id,
        selected_item: this.selected_item
      }
      const response = await axios.post("http://127.0.0.1:5000/api/proof-by-calculation", JSON.stringify(data))
      if (response.data.status == 'ok') {
        this.$set(this.content, this.cur_id, response.data.item)
        this.selected_item = response.data.selected_item
      }
    },

    // First stage of proof by induction: query for induction variable
    proofByInduction: function () {
      this.expr_query1 = "0"
      this.r_query_mode = 'apply induction'
    },

    // Second stage of proof by induction
    doApplyInduction: async function () {
      const data = {
        book: this.book_name,
        file: this.filename,
        content: this.content,
        cur_id: this.cur_id,
        selected_item: this.selected_item,
        induct_var: this.induct_var,
        start: this.expr_query1
      }
      const response = await axios.post("http://127.0.0.1:5000/api/proof-by-induction", JSON.stringify(data))
      if (response.data.status == 'ok') {
        this.$set(this.content, this.cur_id, response.data.item)
        this.selected_item = response.data.selected_item
        this.r_query_mode = undefined
      }
    },

    // Perform proof by rewrite goal
    proofByRewriteGoal: async function () {
      const data = {
        book: this.book_name,
        file: this.filename,
        content: this.content,
        cur_id: this.cur_id
      }
      const response = await axios.post("http://127.0.0.1:5000/api/query-theorems", JSON.stringify(data))
      if (response.data.status == 'ok') {
        this.theorems = response.data.theorems
        this.r_query_mode = 'apply rewrite goal'
      }
    },

    doApplyRewriteGoal: async function (index) {
      const data = {
        book: this.book_name,
        file: this.filename,
        content: this.content,
        cur_id: this.cur_id,
        selected_item: this.selected_item,
        begin: this.theorems[index].eq
      }
      const response = await axios.post("http://127.0.0.1:5000/api/proof-by-rewrite-goal", JSON.stringify(data))
      if (response.data.status == 'ok') {
        this.$set(this.content, this.cur_id, response.data.item)
        this.selected_item = response.data.selected_item
      }
    },

    // Simple form of applying a rule
    applyRule: async function (rulename) {
      const data = {
        book: this.book_name,
        file: this.filename,
        content: this.content,
        cur_id: this.cur_id,
        selected_item: this.selected_item,
        rule: {
          name: rulename
        }
      }
      const response = await axios.post("http://127.0.0.1:5000/api/perform-step", JSON.stringify(data))
      if (response.data.status == 'ok') {
        this.$set(this.content, this.cur_id, response.data.item)
        this.selected_item = response.data.selected_item
      }
    },

    // Expand definition
    expandDefinition: async function () {
      const data = {
        book: this.book_name,
        file: this.filename,
        content: this.content,
        cur_id: this.cur_id,
        selected_item: this.selected_item
      }
      const response = await axios.post("http://127.0.0.1:5000/api/expand-definition", JSON.stringify(data))
      if (response.data.status == 'ok') {
        this.$set(this.content, this.cur_id, response.data.item)
        this.selected_item = response.data.selected_item
      } else if (response.data.status == 'choose') {
        this.def_choices = response.data.choices
        this.r_query_mode = 'expand definition'
      }
    },

    // Second stage of expand definition
    doExpandDefinition: async function (index) {
      const data = {
        book: this.book_name,
        file: this.filename,
        content: this.content,
        cur_id: this.cur_id,
        selected_item: this.selected_item,
        rule: {
          name: "ExpandDefinition",
          func_name: this.def_choices[index].func_name,
          loc: this.def_choices[index].loc
        }
      }
      const response = await axios.post("http://127.0.0.1:5000/api/perform-step", JSON.stringify(data))
      if (response.data.status == 'ok') {
        this.$set(this.content, this.cur_id, response.data.item)
        this.selected_item = response.data.selected_item
        this.r_query_mode = undefined
      }
    },

    // Fold definition
    foldDefinition: async function () {
      const data = {
        book: this.book_name,
        file: this.filename,
        content: this.content,
        cur_id: this.cur_id,
        selected_item: this.selected_item
      }
      const response = await axios.post("http://127.0.0.1:5000/api/fold-definition", JSON.stringify(data))
      if (response.data.status == 'ok') {
        this.$set(this.content, this.cur_id, response.data.item)
        this.selected_item = response.data.selected_item
      }
    },

    // First stage of integrate by parts: query for list of integrals
    integrateByParts: async function () {
      const data = {
        book: this.book_name,
        file: this.filename,
        content: this.content,
        cur_id: this.cur_id,
        selected_item: this.selected_item
      }
      const response = await axios.post("http://127.0.0.1:5000/api/query-integral", JSON.stringify(data))
      if (response.data.status == 'ok') {
        this.sep_int = response.data.integrals
        this.r_query_mode = 'integrate by parts'
      }
    },

    // Second stage of integrate by parts
    doIntegrateByParts: async function () {
      const data = {
        book: this.book_name,
        file: this.filename,
        content: this.content,
        cur_id: this.cur_id,
        selected_item: this.selected_item,
        rule: {
          name: "IntegrationByParts",
          u: this.expr_query1,
          v: this.expr_query2
        }
      }
      const response = await axios.post("http://127.0.0.1:5000/api/perform-step", JSON.stringify(data))
      if (response.data.status == 'ok') {
        this.$set(this.content, this.cur_id, response.data.item)
        this.selected_item = response.data.selected_item
        this.r_query_mode = undefined
      }
    },

    // First stage of forward substitution: query for list of integrals
    forwardSubstitution: async function () {
      const data = {
        book: this.book_name,
        file: this.filename,
        content: this.content,
        cur_id: this.cur_id,
        selected_item: this.selected_item
      }
      const response = await axios.post("http://127.0.0.1:5000/api/query-integral", JSON.stringify(data))
      if (response.data.status == 'ok') {
        this.sep_int = response.data.integrals
        this.r_query_mode = 'forward substitution'
      }
    },

    // Second stage of forward substitution
    doForwardSubstitution: async function () {
      const data = {
        book: this.book_name,
        file: this.filename,
        content: this.content,
        cur_id: this.cur_id,
        selected_item: this.selected_item,
        rule: {
          name: 'Substitution',
          var_name: this.subst_var,
          var_subst: this.expr_query1,
          loc: this.sep_int[this.int_id].loc,
        }
      }
      const response = await axios.post("http://127.0.0.1:5000/api/perform-step", JSON.stringify(data))
      if (response.data.status == 'ok') {
        this.$set(this.content, this.cur_id, response.data.item)
        this.selected_item = response.data.selected_item
        this.r_query_mode = undefined
      }
    },

    // First stage of backward substitution: query for list of integrals
    backwardSubstitution: async function () {
      const data = {
        book: this.book_name,
        file: this.filename,
        content: this.content,
        cur_id: this.cur_id,
        selected_item: this.selected_item,
      }
      const response = await axios.post("http://127.0.0.1:5000/api/query-integral", JSON.stringify(data))
      if (response.data.status == 'ok') {
        this.sep_int = response.data.integrals
        this.int_id = 0
        this.r_query_mode = 'backward substitution'
      }
    },

    // Second stage of backward substitution
    doBackwardSubstitution: async function () {
      const data = {
        book: this.book_name,
        file: this.filename,
        content: this.content,
        cur_id: this.cur_id,
        selected_item: this.selected_item,
        rule: {
          name: 'SubstitutionInverse',
          var_name: this.subst_var,
          var_subst: this.expr_query1,
          loc: this.sep_int[this.int_id].loc
        },
      }
      const response = await axios.post("http://127.0.0.1:5000/api/perform-step", JSON.stringify(data))
      if (response.data.status == 'ok') {
        this.$set(this.content, this.cur_id, response.data.item)
        this.selected_item = response.data.selected_item
        this.r_query_mode = undefined
      }
    },

    // Compute integral by solving equation
    solveEquation: async function () {
      const data = {
        book: this.book_name,
        file: this.filename,
        content: this.content,
        cur_id: this.cur_id,
        selected_item: this.selected_item,
        selected_facts: this.selected_facts
      }
      const response = await axios.post("http://127.0.0.1:5000/api/solve-equation", JSON.stringify(data))
      if (response.data.status == 'ok') {
        this.$set(this.content, this.cur_id, response.data.item)
        this.selected_item = response.data.selected_item
        this.r_query_mode = undefined
        this.selected_facts = {}
      }
    },

    // First stage of rewriting
    rewriteEquation: function () {
      this.selected_expr = undefined
      this.latex_selected_expr = undefined
      this.r_query_mode = 'rewrite equation'
    },

    // Select expression during rewriting
    selectExpr: async function () {
      const start = this.$refs.select_expr1.selectionStart
      const end = this.$refs.select_expr1.selectionEnd
      this.selected_expr = this.lastExpr.slice(start, end)
      const data = {
        expr: this.lastExpr,
        selected_expr: this.selected_expr
      }
      const response = await axios.post("http://127.0.0.1:5000/api/query-latex-expr", JSON.stringify(data))
      if (response.data.status === 'ok') {
        this.latex_selected_expr = response.data.latex_expr,
          this.selected_loc = response.data.loc
      }
    },

    // Perform rewriting
    doRewriteEquation: async function () {
      const data = {
        book: this.book_name,
        file: this.filename,
        content: this.content,
        cur_id: this.cur_id,
        selected_item: this.selected_item,
        rule: {
          name: "Equation",
          old_expr: this.selected_expr,
          new_expr: this.expr_query1
        }
      }
      const response = await axios.post("http://127.0.0.1:5000/api/perform-step", JSON.stringify(data))
      if (response.data.status == 'ok') {
        this.$set(this.content, this.cur_id, response.data.item)
        this.selected_item = response.data.selected_item
        this.r_query_mode = undefined
      }
    },

    // First stage of rewriting using identity
    rewriteUsingIdentity: function () {
      this.selected_expr = undefined
      this.latex_selected_expr = undefined
      this.identity_rewrites = []
      this.r_query_mode = 'rewrite using identity'
    },

    // Select expressiong during rewriting using identity
    selectExprIdentity: async function () {
      const start = this.$refs.select_expr1.selectionStart
      const end = this.$refs.select_expr1.selectionEnd
      this.selected_expr = this.lastExpr.slice(start, end)
      const data = {
        book: this.book_name,
        file: this.filename,
        content: this.content,
        cur_id: this.cur_id,
        selected_item: this.selected_item,
        expr: this.selected_expr
      }
      const response = await axios.post("http://127.0.0.1:5000/api/query-identities", JSON.stringify(data))
      console.log(response.data)
      if (response.data.status === 'ok') {
        this.latex_selected_expr = response.data.latex_expr
        this.identity_rewrites = response.data.results
      }
    },

    // Perform rewriting using identity
    applyIdentity: async function (index) {
      const data = {
        book: this.book_name,
        file: this.filename,
        content: this.content,
        cur_id: this.cur_id,
        selected_item: this.selected_item,
        rule: {
          name: "ApplyIdentity",
          source: this.selected_expr,
          target: this.identity_rewrites[index].res
        }
      }
      const response = await axios.post("http://127.0.0.1:5000/api/perform-step", JSON.stringify(data))
      if (response.data.status == 'ok') {
        this.$set(this.content, this.cur_id, response.data.item)
        this.selected_item = response.data.selected_item
        this.r_query_mode = undefined
      }
    },

    // First stage of split region: query for splitting point
    splitRegion: function () {
      this.r_query_mode = 'split region'
    },

    // Second stage of split region
    doSplitRegion: async function () {
      const data = {
        book: this.book_name,
        file: this.filename,
        content: this.content,
        cur_id: this.cur_id,
        selected_item: this.selected_item,
        rule: {
          name: "SplitRegion",
          c: this.expr_query1
        }
      }
      const response = await axios.post("http://127.0.0.1:5000/api/perform-step", JSON.stringify(data))
      if (response.data.status == 'ok') {
        this.$set(this.content, this.cur_id, response.data.item)
        this.selected_item = response.data.selected_item
        this.r_query_mode = undefined
      }
    },

    // First stage of apply theorem: select theorem to apply
    applyTheorem: async function () {
      const data = {
        book: this.book_name,
        file: this.filename,
        content: this.content,
        cur_id: this.cur_id
      }
      const response = await axios.post("http://127.0.0.1:5000/api/query-theorems", JSON.stringify(data))
      if (response.data.status == 'ok') {
        this.theorems = response.data.theorems
        this.selected_expr = undefined
        this.latex_selected_expr = undefined
        this.r_query_mode = 'select theorem'
      }
    },

    // Second stage of apply theorem.
    doApplyTheorem: async function (index) {
      const data = {
        book: this.book_name,
        file: this.filename,
        content: this.content,
        cur_id: this.cur_id,
        selected_item: this.selected_item,
        rule: {
          name: "ApplyEquation",
          eq: this.theorems[index].eq,
          loc: this.selected_loc
        }
      }
      const response = await axios.post("http://127.0.0.1:5000/api/perform-step", JSON.stringify(data))
      if (response.data.status == 'ok') {
        this.$set(this.content, this.cur_id, response.data.item)
        this.selected_item = response.data.selected_item
        this.r_query_mode = undefined
      }
    },

    // First stage of variable substitution
    variableSubstitution: async function () {
      const data = {
        book: this.book_name,
        file: this.filename,
        content: this.content,
        cur_id: this.cur_id,
        selected_item: this.selected_item
      }
      const response = await axios.post("http://127.0.0.1:5000/api/query-vars", JSON.stringify(data))
      if (response.data.status == 'ok') {
        this.query_vars = response.data.query_vars
        this.r_query_mode = 'query vars'
      }
    },

    // Second stage of variable substitution
    doVariableSubstitution: async function () {
      const data = {
        book: this.book_name,
        file: this.filename,
        content: this.content,
        cur_id: this.cur_id,
        selected_item: this.selected_item,
        rule: {
          name: "VarSubsOfEquation",
          subst: this.query_vars
        }
      }
      const response = await axios.post("http://127.0.0.1:5000/api/perform-step", JSON.stringify(data))
      if (response.data.status == 'ok') {
        this.$set(this.content, this.cur_id, response.data.item)
        this.selected_item = response.data.selected_item
        this.r_query_mode = undefined
      }
    },

    // First stage of differentiate both sides
    applyDerivBothSides: function () {
      this.r_query_mode = 'derivate both sides'
    },

    // Second stage of differentiate both sides
    doApplyDerivBothSides: async function () {
      const data = {
        book: this.book_name,
        file: this.filename,
        content: this.content,
        cur_id: this.cur_id,
        selected_item: this.selected_item,
        rule: {
          name: "DerivEquation",
          var: this.deriv_var
        }
      }
      const response = await axios.post("http://127.0.0.1:5000/api/perform-step", JSON.stringify(data))
      if (response.data.status == 'ok') {
        this.$set(this.content, this.cur_id, response.data.item)
        this.selected_item = response.data.selected_item
        this.r_query_mode = undefined
      }
    },

    // Slagle algorithm
    slagleAlgo: async function () {
      const data = {
        book: this.book_name,
        file: this.filename,
        content: this.content,
        cur_id: this.cur_id,
        selected_item: this.selected_item
      }
      const response = await axios.post("http://127.0.0.1:5000/api/perform-slagle", JSON.stringify(data))
      if (response.data.status == 'ok') {
        this.$set(this.content, this.cur_id, response.data.item)
        this.selected_item = response.data.selected_item
        this.r_query_mode = undefined
      }
    },

    // First stage of solving equation
    solveEquation2: function () {
      this.selected_expr = undefined
      this.latex_selected_expr = undefined
      this.r_query_mode = 'solve equation'
    },

    // Second stage of solving equation
    doSolveEquation: async function () {
      const data = {
        book: this.book_name,
        file: this.filename,
        content: this.content,
        cur_id: this.cur_id,
        selected_item: this.selected_item,
        rule: {
          name: "SolveEquation",
          solve_for: this.selected_expr
        }
      }
      const response = await axios.post("http://127.0.0.1:5000/api/perform-step", JSON.stringify(data))
      if (response.data.status == 'ok') {
        this.$set(this.content, this.cur_id, response.data.item)
        this.selected_item = response.data.selected_item
        this.r_query_mode = undefined
      }
    },

    // First stage of taking limit
    applyLimitBothSides: function () {
      this.r_query_mode = 'limit both sides'
    },

    // Second stage of taking limit
    doApplyLimitBothSides: async function () {
      const data = {
        book: this.book_name,
        file: this.filename,
        content: this.content,
        cur_id: this.cur_id,
        selected_item: this.selected_item,
        rule: {
          name: "LimitEquation",
          var: this.limit_var,
          lim: this.expr_query1
        }
      }
      const response = await axios.post("http://127.0.0.1:5000/api/perform-step", JSON.stringify(data))
      if (response.data.status == 'ok') {
        this.$set(this.content, this.cur_id, response.data.item)
        this.selected_item = response.data.selected_item
        this.r_query_mode = undefined
      }
    },

    // First stage of series expansion
    applySeriesExpansion: function () {
      this.selected_expr = undefined
      this.latex_selected_expr = undefined
      this.r_query_mode = 'series expansion'
    },

    // Second stage of series expansion
    doApplySeriesExpansion: async function () {
      const data = {
        book: this.book_name,
        file: this.filename,
        content: this.content,
        cur_id: this.cur_id,
        selected_item: this.selected_item,
        rule: {
          name: "SeriesExpansionIdentity",
          old_expr: this.selected_expr,
          index_var: this.index_var
        }
      }
      const response = await axios.post("http://127.0.0.1:5000/api/perform-step", JSON.stringify(data))
      if (response.data.status == 'ok') {
        this.$set(this.content, this.cur_id, response.data.item)
        this.selected_item = response.data.selected_item
        this.r_query_mode = undefined
      }
    },

    // First stage of expand polynomial
    applyExpandPolynomial: function () {
      this.r_query_mode = 'expand polynomial'
    },

    // Second stage of expand polynomial
    doApplyExpandPolynomial: async function () {
      const data = {
        book: this.book_name,
        file: this.filename,
        content: this.content,
        cur_id: this.cur_id,
        selected_item: this.selected_item,
        rule: {
          name: "ExpandPolynomial",
          loc: this.selected_loc
        }
      }
      const response = await axios.post("http://127.0.0.1:5000/api/perform-step", JSON.stringify(data))
      if (response.data.status == 'ok') {
        this.$set(this.content, this.cur_id, response.data.item)
        this.selected_item = response.data.selected_item
        this.r_query_mode = undefined
      }
    }
  },

  created: function () {
    this.loadBookList()
    this.book_name = 'interesting'
    this.loadBookContent()
  }
}
</script>

<style scoped>

#content {
  display: inline-block;
  width: 25%;
  position: fixed;
  top: 48px;
  bottom: 0px;
  left: 0px;
  overflow-y: scroll;
  padding-left: 10px;
  padding-top: 5px;
  font-size: large;
}

#calc {
  display: inline-block;
  width: 75%;
  position: fixed;
  top: 48px;
  bottom: 30%;
  left: 25%;
  overflow-y: scroll;
  padding-left: 10px;
  padding-top: 10px;
}

#items {
  display: inline-block;
  width: 75%;
  position: fixed;
  top: 48px;
  bottom: 30%;
  left: 25%;
  overflow-y: scroll;
  padding-left: 10px;
  padding-top: 10px;
  font-size: 20px;
}

#problem {
  display: inline-block;
  width: 75%;
  position: fixed;
  top: 48px;
  bottom: 30%;
  left: 25%;
  overflow-y: scroll;
  padding-left: 10px;
  padding-top: 10px;
  font-size: 20px;
}

#dialog {
  display: inline-block;
  width: 55%;
  height: 30%;
  left: 45%;
  position: fixed;
  top: 70%;
  bottom: 0px;
  padding-left: 10px;
  padding-top: 10px;
  border-top-style: solid;
  overflow-y: scroll;
}

#select {
  display: inline-block;
  width: 20%;
  height: 30%;
  left: 25%;
  position: fixed;
  top: 70%;
  bottom: 0px;
  padding-left: 10px;
  padding-top: 10px;
  border-top-style: solid;
  overflow-y: scroll;
}
.MathJax_Display {
  color: rgb(255, 255, 255) !important;
}

</style>