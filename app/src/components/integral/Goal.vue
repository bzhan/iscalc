<template>
  <div class="indented-label">
    <span class="math-text">{{label}}</span>&nbsp;
    <div>
      <span class="math-text">Show</span>
      <div @click.exact="$emit('select', label)"
           @click.ctrl="$emit('select_fact', label)"
           :class="{selected: selected_item == label,
                    'selected-fact': label in selected_facts}">
        <MathEquation v-bind:data="'\\(' + item.latex_goal + '\\)'" class="indented-text"/>
        <span v-if="'conds' in item && item.conds.length > 0">
          <span class="math-text indented-text">for &nbsp;</span>
          <span v-for="(cond, index) in item.conds" :key="index">
            <span v-if="index > 0">, &nbsp;</span>
            <MathEquation v-bind:data="'\\(' + cond.latex_cond + '\\)'"/>
          </span>
        </span>
        <span v-if="'fixes' in item && item.fixes.length > 0">
          <br> &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; &nbsp;
          <span class="math-text indented-text">where &nbsp;</span>
          <span v-for="(info, index) in item.fixes" :key="index">
            <span v-if="index > 0">, &nbsp;</span>
            <MathEquation v-bind:data="'\\(' + info[1].latex_type + '\\)'"/>
          </span>
        </span>

        <span v-if="'wellformed' in item && item.wellformed == false"
              title="Unable to show wellformed">
          ⚠
        </span>
      </div>
      <!-- Proof content -->
      <div v-if="'proof' in item">
        <div v-if="item.proof.type === 'CalculationProof'">
          <CalculationProof v-bind:item="item.proof" v-bind:label="label"
                            v-bind:selected_item="selected_item"
                            v-bind:selected_facts="selected_facts"
                            @select="(lbl) => $emit('select', lbl)"/>
        </div>
        <div v-if="item.proof.type === 'InductionProof'">
          <InductionProof v-bind:item="item.proof" v-bind:label="label"
                          v-bind:selected_item="selected_item"
                          v-bind:selected_facts="selected_facts"
                          v-bind:start_point = "start_point"
                          @select="(lbl) => $emit('select', lbl)"/>
        </div>
        <div v-if="item.proof.type === 'RewriteGoalProof'">
          <RewriteGoalProof v-bind:item="item.proof" v-bind:label="label"
                          v-bind:selected_item="selected_item"
                          v-bind:selected_facts="selected_facts"
                          @select="(lbl) => $emit('select', lbl)"/>
        </div>
        <div v-if="item.proof.type === 'CaseProof'">
          <CaseProof v-bind:item="item.proof" v-bind:label="label"
                          v-bind:selected_item="selected_item"
                          v-bind:selected_facts="selected_facts"
                          @select="(lbl) => $emit('select', lbl)"/>
        </div>
      </div>
    </div>
  </div>
</template>

<script>
import MathEquation from '../util/MathEquation.vue'
import CalculationProof from './CalculationProof.vue'
import InductionProof from './InductionProof.vue'
import RewriteGoalProof from './RewriteGoalProof.vue'
import CaseProof from './CaseProof.vue'

export default {
  name: "Goal",
  components: {
    MathEquation,
    CalculationProof,
    InductionProof,
    RewriteGoalProof,
    CaseProof,
  },

  props: [
    "item",
    "label",
    "selected_item",
    "selected_facts",
    "start_point"
  ],

  emits: [
    "select",
    "select_fact"
  ],

  mounted() {
    //console.log("Goal module mounted")
    //console.log("item:",this.item)
    //console.log("start_point", this.start_point)
  }
}

</script>
