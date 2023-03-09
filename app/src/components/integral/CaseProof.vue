<template>
    <div>
      <span class="math-text">split by &nbsp;&nbsp;</span>
      <MathEquation v-bind:data="'\\(' + item.latex_split_cond + '\\)'"/><br/>
      <div v-for="(case_item, index) in item.cases" :key="index">
        <span class="math-text">{{label}}{{index+1}}. Case {{index+1}}: </span>
        <span @click="$emit('select', label + (index+1) + '.')"
              :class="{selected: selected_item == label + (index+1) + '.'}">
          <MathEquation v-bind:data="'\\(' + case_item.latex_goal + '\\)'"/>
        </span>
        <span v-if="'conds' in case_item && case_item.conds.length > 0">
            <span class="math-text indented-text">for &nbsp;</span>
            <span v-for="(cond, index) in case_item.conds" :key="index">
              <span v-if="index > 0">, &nbsp;</span>
              <MathEquation v-bind:data="'\\(' + cond.latex_cond + '\\)'"/>
            </span>
        </span><br/>
        <CalculationProof v-if="'proof' in case_item && case_item.proof.type === 'CalculationProof'"
                          v-bind:item="case_item.proof" v-bind:label="label + (index+1) + '.'"
                          v-bind:selected_item="selected_item"
                          v-bind:selected_facts="selected_facts"
                          @select="(lbl) => $emit('select', lbl)"/>
        <RewriteGoalProof v-if="'proof' in case_item && case_item.proof.type === 'RewriteGoalProof'"
                          v-bind:item="case_item.proof" v-bind:label="label + (index+1) + '.'"
                          v-bind:selected_item="selected_item"
                          v-bind:selected_facts="selected_facts"
                          @select="(lbl) => $emit('select', lbl)"/>
      </div>
    </div>
  </template>
  
  <script>
  import MathEquation from '../util/MathEquation.vue'
  import CalculationProof from './CalculationProof.vue'
  import RewriteGoalProof from './RewriteGoalProof.vue'
  export default {
    name: "CaseProof",
    components: {
      MathEquation,
      CalculationProof,
      RewriteGoalProof,
    },
  
    props: [
      "item",
      "label",
      "selected_item",
      "selected_facts",
    ]
  }
  
  </script>
  