<template>
  <form>
    <div>
      <label>name:</label><input v-model="header_name" />
    </div>
    <div>
      <label>level:</label><input v-model="header_level" />
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
