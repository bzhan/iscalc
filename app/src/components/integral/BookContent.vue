<template>
  <div>
    <div v-if="content.type === 'header'">
      <div @click="selectHeader(label)" 
        :class="{selected: selected_item == label, 
                 'header-1': header_level == 1,
                 'header-2': header_level == 2,
                 'header-3': header_level == 3,
                 'header-4': header_level == 4,
                 'header-5': header_level == 5}" 
        v-bind:selected_item="selected_item">{{ content.name }}</div>
      <div v-for="(item, index) in content.content" :key="index">
        <BookContent  v-bind:content="item" @open_file="openFile" @select_header = "selectHeader" 
                      v-bind:label="label+(index+1)+'.'"
                      v-bind:selected_item="selected_item"
                      v-bind:header_level="header_level+1"></BookContent>
      </div>
    </div>
    <div v-else>
      <div v-if="content.type == 'definition'">
        <MathEquation v-bind:data="'\\(' + content.latex_str + '\\)'" class="indented-text"
          v-on:click.native="openFile(content.path)"
          style="cursor:pointer"/>
      </div>
      <div v-if="content.type == 'problem'">
        <MathEquation v-bind:data="'\\(' + content.latex_str + '\\)'" class="indented-text"
          v-on:click.native="openFile(content.path)"
          style="cursor:pointer"/>
        <span v-if="'latex_conds' in content && content.latex_conds.length > 0">
          <span class="math-text indented-text">for &nbsp;</span>
          <span v-for="(cond, index) in content.latex_conds" :key="index">
            <span v-if="index > 0">, &nbsp;</span>
            <MathEquation v-bind:data="'\\(' + cond + '\\)'"/>
          </span>
        </span>
      </div>
      <div v-if="content.type == 'axiom'">
        <MathEquation v-bind:data="'\\(' + content.latex_str + '\\)'" class="indented-text"/>
        <span v-if="'latex_conds' in content && content.latex_conds.length > 0">
          <span class="math-text indented-text">for &nbsp;</span>
          <span v-for="(cond, index) in content.latex_conds" :key="index">
            <span v-if="index > 0">, &nbsp;</span>
            <MathEquation v-bind:data="'\\(' + cond + '\\)'"/>
          </span>
        </span>
      </div>
      <div v-if="content.type == 'table'" style="margin: 5px">
        <table style="border-collapse: collapse">
          <tr>
            <td style="border-style: solid; padding: 3px">
              <MathEquation v-bind:data="'\\(' + '{x}' + '\\)'"/>
            </td>
            <td v-for="(entry, index) in content.latex_table" :key="index"
                style="border-style: solid; padding: 3px">
              <MathEquation v-bind:data="'\\(' + entry.x + '\\)'"/>
            </td>
          </tr>
          <tr>
            <td style="border-style: solid; padding: 3px">
              <MathEquation v-bind:data="'\\(' + content.funcexpr + '\\)'"/>
            </td>
            <td v-for="(entry, index) in content.latex_table" :key="index"
                style="border-style: solid; padding: 3px">
              <MathEquation v-bind:data="'\\(' + entry.y + '\\)'"/>
            </td>
          </tr>
        </table>
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
    'content',
    'label',
    'selected_item',
    'header_level',
  ],
  methods: {
    openFile: function(name){
      this.$emit('open_file', name)
    },
    selectHeader: function(label) {
      this.$emit('select_header', label)
    }
  }
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

.header-4 {
  font-size: medium;
  font-weight: 500;
}

.header-5 {
  font-size: small;
  font-weight: 500;
}
</style>
  