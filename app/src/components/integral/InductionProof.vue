<template>
  <div>
    <span class="math-text">by induction on </span>
    <MathEquation v-bind:data="'\\(' + item.induct_var + '\\)'"/>
    <span class="math-text" v-if="start_point !== undefined"> from </span>
    <MathEquation v-if="start_point !== undefined" v-bind:data="'\\(' + start_point + '\\)'"/>
    <br/>
    <span class="math-text">{{label}}1. Base case: </span>
    <span @click="$emit('select', label + '1.')"
          :class="{selected: selected_item == label + '1.'}">
      <MathEquation v-bind:data="'\\(' + item.base_case.latex_goal + '\\)'"/><br/>
    </span>
    <CalculationProof v-if="'proof' in item.base_case"
                      v-bind:item="item.base_case.proof" v-bind:label="label + '1.'"
                      v-bind:selected_item="selected_item"
                      v-bind:selected_facts="selected_facts"
                      @select="(lbl) => $emit('select', lbl)"/>
    <span class="math-text">{{label}}2. Induction case: </span>
    <span @click="$emit('select', label + '2.')"
          :class="{selected: selected_item == label + '2.'}">
      <MathEquation v-bind:data="'\\(' + item.induct_case.latex_goal + '\\)'"/><br/>
    </span>
    <CalculationProof v-if="'proof' in item.induct_case"
                      v-bind:item="item.induct_case.proof" v-bind:label="label + '2.'"
                      v-bind:selected_item="selected_item"
                      v-bind:selected_facts="selected_facts"
                      @select="(lbl) => $emit('select', lbl)"/>
  </div>
</template>

<script>
import MathEquation from '../util/MathEquation.vue'
import CalculationProof from './CalculationProof.vue'

export default {
  name: "InductionProof",
  components: {
    MathEquation,
    CalculationProof,
  },

  props: [
    "item",
    "label",
    "selected_item",
    "selected_facts",
    "start_point"
  ]
}

</script>
