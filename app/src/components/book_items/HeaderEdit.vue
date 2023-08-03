<template>
  <form>
    <div>
      <label>name</label>
      <input v-model="name"/>
    </div>
    <div>
      <label>level</label>
      <input v-model="level"/>
    </div>
  </form>
</template>

<script>
export default {
  name: 'HeaderEdit',
  props: [
    "header"
  ],

  data: function () {
    return {
      name: this.header.name,
      level: this.header.level
    }
  }
}
</script>
