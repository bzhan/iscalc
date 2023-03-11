<template>
  <div>
    <div v-for="(item, index) in content" :key="index">
    <div v-if="item.type == 'header'">
        <span>{{ item.name }}</span>
        <BookContent v-bind:content="item.content" @open_file="openFile"></BookContent>
      </div>
      
      <div v-else>
        <div v-if="item.type == 'definition'">
          <MathEquation v-bind:data="'\\(' + item.latex_str + '\\)'" class="indented-text"
            v-on:click.native="openFile(item.path)"
            style="cursor:pointer"/>
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
        </div>
        <div v-if="item.type == 'axiom'">
          <MathEquation v-bind:data="'\\(' + item.latex_str + '\\)'" class="indented-text"/>
          <span v-if="'latex_conds' in item && item.latex_conds.length > 0">
            <span class="math-text indented-text">for &nbsp;</span>
            <span v-for="(cond, index) in item.latex_conds" :key="index">
              <span v-if="index > 0">, &nbsp;</span>
              <MathEquation v-bind:data="'\\(' + cond + '\\)'"/>
            </span>
          </span>
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
        </div>
      </div>
    </div>
  </div>
</template>
  
  <script>
  import MathEquation from '../util/MathEquation.vue'
  
  export default {
    name: "BookContent",
    components: {
      MathEquation
    },
    props: [
      'content'
    ],
    methods: {
      openFile: function(name){
        this.$emit('open_file', name)
      }
    }
  }
  
  </script>
  