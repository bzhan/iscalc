<template>
  <div>
    <span class="math-text">by calculation</span>
    <span v-if="item.finished" class="math-text" style="color: green">&nbsp;(finished)</span><br/>
    <div v-for="(calc_item, index) in item.calcs" :key="index">
      <span class="math-text">{{label}}{{index+1}}.</span>&nbsp;
      <Calculation v-bind:item="calc_item" v-bind:label="label + (index+1) + '.'"
                  v-bind:selected_item="selected_item"
                  v-bind:selected_facts="selected_facts"
                  @select="(lbl) => $emit('select', lbl)"/>
    </div>
  </div>
</template>

<script>
import Calculation from './Calculation.vue'

export default {
  name: "CalculationProof",
  components: {
    Calculation,
  },

  props: [
    "item",
    "label",
    "selected_item",
    "selected_facts",
  ]
}

</script>
