<template>
  <div>
    <div v-if=" content.content !== undefined && content.content[0] === undefined">
      <a v-if="add_pos === undefined" href="#" v-on:click="add_pos = 0" title="add item" style="margin-left:10px">
        <v-icon name="plus"/>
      </a>
      <div v-if="add_pos === 0">
          <form>
            <div>
              <label>item type:</label>
              <select v-model="item_type">
                <option v-for="(type, index) in item_types" :key="index">{{ type }}</option>
              </select>
            </div>
            <div v-if="item_type === 'header'">
              <lable>name:</lable>
              <input v-model="header_name"/><br>
            </div>
            <div v-if="item_type === 'header'">
              <lable>level:</lable>
              <input v-model="header_level"/><br>
            </div>
            <!-- goal of problem -->
            <div v-if="item_type === 'problem'">
              <ExprQuery :label="'expr_latex: '" v-model="problem_expr"></ExprQuery>
            </div>
            <!-- fixes of problem -->
            <div v-if="item_type === 'problem'">
              <div v-for="(item, index) in problem_fixes" :key="index">
                <ExprQuery :label="'var_'+index+': '" v-bind:value="item.var"
                          @input="setProblemFixes(index, {'type':item.type, 'var':$event})"/><br/>
                <ExprQuery :label="'type_'+index+': '" v-bind:value="item.type" 
                          @input="setProblemFixes(index, {'type':$event, 'var':item.var})"/><br/>
              </div>
              <button v-on:click="problem_fixes.push({'type': undefined, 'var':undefined})">Add fixes</button>
            </div>
            <!-- conds of problem -->
            <div v-if="item_type === 'problem'">
              <div v-for="(cond, index) in problem_conds" :key="index">
                <ExprQuery :label="'cond_'+index+': '" v-bind:value="cond" 
                          @input="setProblemConds(index, $event)"/><br/>
              </div>
              <button v-on:click="problem_conds.push('')">Add condition</button>
            </div>
            <div v-if = "item_type === 'problem'">
              <label>path:</label>
              <input v-model="problem_path"/><br/>
            </div>
            <div v-if = "item_type === 'definition'">
              <ExprQuery :label="'expr_latex: '" v-model="definition_expr"></ExprQuery>
            </div>
            <div v-if = "item_type === 'axiom'">
              <ExprQuery :label="'expr_latex: '" v-model="axiom_expr"></ExprQuery>
            </div>
            <div v-if = "item_type === 'axiom'">
              <label>category:</label>
              <input v-model="axiom_category"/><br/>
            </div>
            <div v-if = "item_type === 'axiom'">
              <!-- attributes -->
            </div>

          </form>
          <button v-if="item_type === 'header'" style="margin:5px" v-on:click="add_header(0)">Add</button>
          <button v-if="item_type === 'problem'" style="margin:5px" v-on:click="add_problem(0)">Add</button>
          <button v-if="item_type === 'definition'" style="margin:5px" v-on:click="add_definition(0)">Add</button>
          <button v-if="item_type === 'axiom'" style="margin:5px" v-on:click="add_axiom(0)">Add</button>
          <button style="margin:5px" v-on:click="add_pos = undefined">Cancel</button>
      </div>
    </div>
    <div v-else>
      <div v-for="(item, idx) in content.content" :key="idx">
        <div v-if="item.type === 'header'"
            v-bind:class="{'item-selected':is_selected(idx)}"
            v-on:click="selected_item=idx">
          <div v-if="edit_pos === undefined || edit_pos !== idx">
            <span v-html="item.name"
                  :class="{'header-1': item.level == 1,
                          'header-2': item.level == 2,
                          'header-3': item.level == 3}"></span>
            <a href="#" v-on:click="edit_pos = idx" title="edit" style="margin-left:10px">
              <v-icon name="edit"/>
            </a>
            <a href="#" v-on:click="add_pos = idx" title="add item" style="margin-left:10px">
              <v-icon name="plus"/>
            </a>
          </div>
          <div v-else>
            <HeaderEdit :header="content.content[idx]" ref="edit"></HeaderEdit>
            <button style="margin:5px" v-on:click="save_header(idx)">Save</button>
            <button style="margin:5px" v-on:click="edit_pos = undefined">Cancel</button>
          </div>
        </div>
        <div v-else>
          <div v-if="item.type == 'definition'">
            <MathEquation v-bind:data="'\\(' + item.latex_str + '\\)'" class="indented-text"
              style="cursor:pointer"/>
            <a href="#" v-on:click="edit_header = true" title="edit" style="margin-left:10px">
              <v-icon name="edit"/>
            </a>
            <a href="#" v-on:click="add_pos = idx" title="add item" style="margin-left:10px">
              <v-icon name="plus"/>
            </a>
          </div>
          <div v-if="item.type == 'problem'">
            <MathEquation v-bind:data="'\\(' + item.latex_str + '\\)'" class="indented-text"
              v-on:click.native="openFile(item.path)"
              style="cursor:pointer"/>
            <span v-if="'latex_conds' in item && item.latex_conds.length > 0">
              <span class="math-text indented-text">for &nbsp;</span>
              <span v-for="(cond, index) in item.latex_conds" :key="index">
                <span v-if="index > 0">, &nbsp;</span>
                <MathEquation v-bind:data="'\\(' + cond + '\\)'"/>
              </span>
            </span>
            <a href="#" v-on:click="edit_header = true" title="edit" style="margin-left:10px">
              <v-icon name="edit"/>
            </a>
            <a href="#" v-on:click="add_pos = idx" title="add item" style="margin-left:10px">
              <v-icon name="plus"/>
            </a>
          </div>
          <div v-if="item.type == 'axiom' || item.type == 'inequality'">
            <MathEquation v-bind:data="'\\(' + item.latex_str + '\\)'" class="indented-text"/>
            <span v-if="'latex_conds' in item && item.latex_conds.length > 0">
              <span class="math-text indented-text">for &nbsp;</span>
              <span v-for="(cond, index) in item.latex_conds" :key="index">
                <span v-if="index > 0">, &nbsp;</span>
                <MathEquation v-bind:data="'\\(' + cond + '\\)'"/>
              </span>
            </span>
            <a href="#" v-on:click="edit_header = true" title="edit" style="margin-left:10px">
              <v-icon name="edit"/>
            </a>
            <a href="#" v-on:click="add_pos = idx" title="add item" style="margin-left:10px">
              <v-icon name="plus"/>
            </a>
          </div>
          <div v-if="item.type == 'table'" style="margin: 5px">
            <table style="border-collapse: collapse">
              <tr>
                <td style="border-style: solid; padding: 3px">
                  <MathEquation v-bind:data="'\\(' + '{x}' + '\\)'"/>
                </td>
                <td v-for="(entry, index) in item.latex_table" :key="index"
                    style="border-style: solid; padding: 3px">
                  <MathEquation v-bind:data="'\\(' + entry.x + '\\)'"/>
                </td>
              </tr>
              <tr>
                <td style="border-style: solid; padding: 3px">
                  <MathEquation v-bind:data="'\\(' + item.funcexpr + '\\)'"/>
                </td>
                <td v-for="(entry, index) in item.latex_table" :key="index"
                    style="border-style: solid; padding: 3px">
                  <MathEquation v-bind:data="'\\(' + entry.y + '\\)'"/>
                </td>
              </tr>
            </table>
            <a href="#" v-on:click="edit_header = true" title="edit" style="margin-left:10px">
                <v-icon name="edit"/>
            </a>
            <a href="#" v-on:click="add_pos = idx" title="add item" style="margin-left:10px">
                <v-icon name="plus"/>
            </a>
          </div>
        </div>
        <div v-if="add_pos === idx">
          <form>
            <div>
              <label>item type:</label>
              <select v-model="item_type">
                <option v-for="(type, index) in item_types" :key="index">{{ type }}</option>
              </select>
            </div>
            <div>
              <label>insert position:</label>
              <select v-model="insert_pos">
                <option>previous</option>
                <option>next</option>
              </select>
            </div>
            <div v-if="item_type === 'header'">
              <lable>name:</lable>
              <input v-model="header_name"/><br>
            </div>
            <div v-if="item_type === 'header'">
              <lable>level:</lable>
              <input v-model="header_level"/><br>
            </div>
            <div v-if="item_type === 'problem'">
              <ExprQuery :label="'expr_latex: '" v-model="problem_expr"></ExprQuery>
            </div>
            <!-- fixes of problem -->
            <div v-if="item_type === 'problem'">
              <div v-for="(item, index) in problem_fixes" :key="index">
                <ExprQuery :label="'var_'+index+': '" v-bind:value="item.var"
                          @input="setProblemFixes(index, {'type':item.type, 'var':$event})"/><br/>
                <ExprQuery :label="'type_'+index+': '" v-bind:value="item.type" 
                          @input="setProblemFixes(index, {'type':$event, 'var':item.var})"/><br/>
              </div>
              <button v-on:click="problem_fixes.push({'type': undefined, 'var':undefined})">Add fixes</button>
            </div>
            <div v-if="item_type === 'problem'">
              <div v-for="(cond, index) in problem_conds" :key="index">
                <ExprQuery :label="'cond_'+index+': '" v-bind:value="cond" 
                          @input="setProblemConds(index, $event)"/><br/>
              </div>
              <button v-on:click="problem_conds.push('')">Add condition</button>
            </div>

            <div v-if = "item_type === 'problem'">
              <label>path:</label>
              <input v-model="problem_path"/><br/>
            </div>
            <div v-if = "item_type === 'definition'">
              <ExprQuery :label="'expr_latex: '" v-model="definition_expr"></ExprQuery>
            </div>
            <div v-if = "item_type === 'axiom'">
              <ExprQuery :label="'expr_latex: '" v-model="axiom_expr"></ExprQuery>
            </div>
            <div v-if = "item_type === 'axiom'">
              <label>category:</label>
              <input v-model="axiom_category"/><br/>
            </div>
            <div v-if = "item_type === 'axiom'">
              <!-- attributes -->
            </div>

          </form>
          <button v-if="item_type === 'header'" style="margin:5px" v-on:click="add_header(idx)">Add</button>
          <button v-if="item_type === 'problem'" style="margin:5px" v-on:click="add_problem(idx)">Add</button>
          <button v-if="item_type === 'definition'" style="margin:5px" v-on:click="add_definition(idx)">Add</button>
          <button v-if="item_type === 'axiom'" style="margin:5px" v-on:click="add_axiom(idx)">Add</button>
          <button style="margin:5px" v-on:click="add_pos = undefined">Cancel</button>
        </div>
      </div>
    </div>
  </div>
</template>
<script>
import axios from 'axios'
import MathEquation from '../util/MathEquation.vue'
import HeaderEdit from '../book_items/HeaderEdit'
import ExprQuery from './ExprQuery'
export default {
  name: "BookContent",
  components: {
    MathEquation,
    HeaderEdit,
    ExprQuery
  },
  data: function(){
    return {
      axiom_category: undefined,
      axiom_expr: undefined,
      edit_pos:undefined,
      selected_item:undefined,
      add_pos:undefined,
      insert_pos:undefined,
      item_types: ['header', 'axiom', 'table', 'definition', 'problem'],
      item_type: undefined,
      header_name: undefined,
      header_level: undefined,
      is_next: undefined,
      problem_expr: undefined,
      problem_conds: [],
      problem_fixes: [],
      problem_path: undefined,
      definition_expr: undefined,
    }
  },
  props: [
    'content',
    'book_name'
  ],
  methods: {
    openFile: function(name){
      this.$emit('open_file', name)
    },
    /*
    selectItem: function(index) {
      this.$emit('select_book_item', index)
    },
    */
    save_book: async function() {
      
      const data = {
        filename: this.book_name,
        content: this.content,
        type: 'book'
      }
      const response = await axios.post("http://127.0.0.1:5000/api/integral-save-file", JSON.stringify(data))
      if (response.data.status === 'ok') {
        console.log("ok")
      }
      
    },
    save_header: async function(idx) {
      this.$nextTick(async () => {
        const data = {
          'item':{
            'name': this.$refs.edit[0].name,
            'level': this.$refs.edit[0].level,
            'type': 'header'
          },
          'filename': this.book_name,
          'index': idx
        }
        const response = await axios.post("http://127.0.0.1:5000/api/integral-save-book-item", JSON.stringify(data))
        if (response.data.status === 'ok') {
          this.$parent.loadBookContent();
          console.log("ok")
        }
        this.init_var()
      })
    },
    is_selected: function(idx) {
      return idx === this.selected_item
    },
    init_var: function() {
      this.add_pos = undefined
      this.problem_conds = []
      this.problem_fixes = []
      this.problem_expr = undefined
      this.item_type = undefined
      this.definition_expr = undefined
      this.edit_pos = undefined
    },
    add_header: async function(idx) {
      var pos = idx 
      if(this.insert_pos !== undefined && this.insert_pos == 'next')
        pos = idx + 1
      const data = {
        'item':{
          'name': this.header_name,
          'level': Number(this.header_level),
          'type': this.item_type
        },
        'filename': this.book_name,
        'index': pos
      }
      const response = await axios.post("http://127.0.0.1:5000/api/integral-book-add-item", JSON.stringify(data))
      if (response.data.status === 'ok') {
        this.$parent.loadBookContent();
        console.log("ok")
      }
      this.init_var()
    },
    add_problem: async function(idx) {
      this.$nextTick(async () => {
        var pos = idx 
        if(this.insert_pos !== undefined && this.insert_pos == 'next')
          pos = idx + 1
        const data = {
          'item':{
            'expr': this.problem_expr,
            'conds': this.problem_conds,
            'path': this.problem_path,
            'type': this.item_type,
            'fixes': this.problem_fixes
          },
          'filename': this.book_name,
          'index': pos
        }
        const response = await axios.post("http://127.0.0.1:5000/api/integral-book-add-item", JSON.stringify(data))
        if (response.data.status === 'ok') {
          this.$parent.loadBookContent();
          console.log("ok")
        }
        this.init_var()
      })
    },
    add_definition: async function(idx) {
      this.$nextTick(async () => {
        var pos = idx 
        if(this.insert_pos !== undefined && this.insert_pos == 'next')
          pos = idx + 1
        const data = {
          'item':{
            'expr': this.definition_expr,
            'type': this.item_type
          },
          'filename': this.book_name,
          'index': pos
        }
        const response = await axios.post("http://127.0.0.1:5000/api/integral-book-add-item", JSON.stringify(data))
        if (response.data.status === 'ok') {
          this.$parent.loadBookContent();
          console.log("ok")
        }
        this.init_var()
      })
    },
    setProblemConds: function(index, value){
      this.$set(this.problem_conds, index, value)
    },
    setProblemFixes: function(index, item){
      this.$set(this.problem_fixes, index, item)
    }
  },
  mounted() {
    console.log(this.content.content)
  },
}

</script>
<style scoped>
.header-1 {
  font-size: xx-large;
  font-weight: 500;
  text-align: center
}

.header-2 {
  font-size: x-large;
  font-weight: 500;
}

.header-3 {
  font-size: large;
  font-weight: 500;
}

.item-selected {
  border-style: solid;
  border-width: thin;
}
</style>
  
