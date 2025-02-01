<template>
    <div class="meta-tree-view">
        <div v-for="(item, index) in data" :key="index" class="meta-tree-node">
            <div class="code-container">
                <div class="node-header" @click="toggleChildren(index)">
                    <span class="toggle-icon">
                        {{ item.childs && item.childs.length ? (isOpen(index) ? '▼' : '▶') : '' }}
                    </span>
                    <span v-if="item.assume_name">({{ item.assume_name }})&nbsp;</span>
                    <span class="initial-form">{{ item.initial_form }}</span>
                </div>
                <div v-if="item.quant_inst.length > 0">Instantiation:
                    <span v-for="inst in item.quant_inst" :key="inst.var">
                        {{inst.var}}: {{ inst.t }} 
                    </span>
                </div>
                <div v-if="item.new_var.length > 0">New variables:
                    <span v-for="(var_name, index) in item.new_var" :key="var_name">
                        {{ var_name }}<span v-if="index < item.new_var.length - 1">, </span>
                    </span>
                </div>

                <!-- Child Nodes -->
                <div v-if="item.childs && item.childs.length && isOpen(index)" class="child-nodes">
                    <MetaTreeView :data="item.childs" />
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
</script>

<style scoped>
.meta-tree-view {
    font-family: Arial, sans-serif;
    margin-left: 20px;
}

.code-container {
    font-family: monospace; /* Set monospace font for all text */
    background-color: white; /* Set background to white */
    padding: 10px; /* Add some padding for better readability */
    border: 1px solid #ccc; /* Optional: Add a border for visual separation */
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

.initial-form {
    white-space: pre; /* Preserve newlines in the text */
}
</style>