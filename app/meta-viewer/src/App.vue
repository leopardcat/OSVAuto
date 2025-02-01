<script setup>
import { ref } from 'vue'; // Import ref for reactive state
import MetaTreeView from './components/MetaTreeView.vue';
import metaJsonData from './assets/meta.json';
import DiagnosticTreeView from './components/DiagnosticTreeView.vue';
import diagnosticJsonData from './assets/diagnostic.json';

const activeTab = ref('meta');
</script>

<template>
  <header>
    <!-- Tabs for switching between panels -->
    <div class="tabs">
      <button
        :class="{ active: activeTab === 'meta' }"
        @click="activeTab = 'meta'"
      >
        Meta
      </button>
      <button
        :class="{ active: activeTab === 'diagnostic' }"
        @click="activeTab = 'diagnostic'"
      >
        Diagnostic
      </button>
    </div>
  </header>

  <main>
    <div v-if="activeTab === 'meta'">
      <div>Assumptions</div>
      <MetaTreeView :data="metaJsonData.assume" />
      <div>Goal</div>
      <MetaTreeView :data="metaJsonData.concl" />
    </div>

    <div v-if="activeTab === 'diagnostic'">
      <div>Assumptions</div>
      <DiagnosticTreeView :data="diagnosticJsonData.assume" />
      <div>Goal</div>
      <DiagnosticTreeView :data="diagnosticJsonData.concl" />
    </div>
  </main>
</template>

<style scoped>
header {
  line-height: 1.5;
}

/* Basic styling for the tabs */
.tabs {
  margin-bottom: 20px;
}

.tabs button {
  padding: 10px 20px;
  margin-right: 10px;
  border: none;
  background-color: #f0f0f0;
  cursor: pointer;
}

.tabs button.active {
  background-color: #007bff;
  color: white;
}
</style>
