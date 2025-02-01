<template>
    <div class="diagnostic-tree-view">
        <div v-for="(item, index) in data" :key="index" class="diagnostic-tree-node">
            <div class="code-container">
                <div class="node-header" @click="toggleChildren(index)">
                    <span class="toggle-icon">
                        {{ item.childs && item.childs.length ? (isOpen(index) ? '▼' : '▶') : '' }}
                    </span>
                    <span class="term" @click.stop="toggleTerm(index)">
                        {{ showFullText[index] ? item.t : item.short_form }}</span>
                    <span class="term">{{ item.eval_t }}</span>
                </div>

                <!-- Child Nodes -->
                <div v-if="item.childs && item.childs.length && isOpen(index)" class="child-nodes">
                    <DiagnosticTreeView :data="item.childs" />
                </div>
            </div>
        </div>
    </div>
</template>

<script setup>
import { ref } from 'vue';

// Props
const props = defineProps({
    data: {
        type: Array,
        required: true,
    },
});

// State for tracking open/closed nodes
const openNodes = ref([]);

// Toggle visibility of child nodes
const toggleChildren = (index) => {
    if (openNodes.value.includes(index)) {
        openNodes.value = openNodes.value.filter((i) => i !== index);
    } else {
        openNodes.value.push(index);
    }
};

// Check if a node is open
const isOpen = (index) => {
    return openNodes.value.includes(index);
};

// Reactive state to track which items show full text (t) or short form
const showFullText = ref([]);

// Function to toggle between short_form and t for a specific item
function toggleTerm(index) {
  showFullText.value[index] = !showFullText.value[index];
}

</script>

<style scoped>
.meta-tree-view {
    font-family: Arial, sans-serif;
    margin-left: 20px;
}

.code-container {
    font-family: monospace;
    /* Set monospace font for all text */
    background-color: white;
    /* Set background to white */
    padding: 10px;
    /* Add some padding for better readability */
    border: 1px solid #ccc;
    /* Optional: Add a border for visual separation */
    width: 80vw;
    margin: 0 auto;
    box-sizing: border-box;
}

.meta-tree-node {
    margin-bottom: 10px;
}

.node-header {
    cursor: pointer;
    display: flex;
    align-items: center;
    padding: 5px;
    background-color: #f0f0f0;
    border-radius: 4px;
}

.toggle-icon {
    margin-right: 10px;
    font-size: 12px;
}

.child-nodes {
    margin-left: 20px;
    margin-top: 10px;
}

.term {
    white-space: pre;
    /* Preserve newlines in the text */
}
</style>