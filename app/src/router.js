import Vue from 'vue'
import VueRouter from 'vue-router'

Vue.use(VueRouter)

import Integral from './components/integral/Integral.vue'

const routes = [
  {path: '/', name: 'main', component: Integral},
]

const router = new VueRouter({
  routes,
  mode: 'history'
})

export default router
